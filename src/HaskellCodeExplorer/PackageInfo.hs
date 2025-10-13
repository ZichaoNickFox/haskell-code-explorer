{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HaskellCodeExplorer.PackageInfo
  ( createPackageInfo
  , ghcVersion
  ) where

import Control.DeepSeq(deepseq)
import Control.Exception
  ( IOException
  , SomeAsyncException
  , SomeException
  , fromException
  , throw
  , try
  )
import Control.Monad (foldM, unless, when)
import Control.Monad.Extra (anyM, findM)
import Control.Monad.Logger
  ( LoggingT(..)
  , MonadLogger(..)
  , MonadLoggerIO(..)
  , logDebugN
  , logErrorN
  , logInfoN
  )
import qualified Data.ByteString as BS
import qualified Data.HashMap.Strict as HM
import Data.IORef (readIORef)
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Data.Maybe (fromMaybe, isJust, maybeToList)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Version (Version(..), showVersion, makeVersion)
import GHC.Driver.Phases (Phase)
import Data.Bool
import GHC.Utils.Logger
  ( getLogger
  , LogFlags(..)
  , pushLogHook )
import GHC.Utils.Error
  ( Severity
  , MessageClass(..) )
import GHC.Types.SrcLoc   (SrcSpan)
import GHC.Utils.Outputable (SDoc, showSDocUnsafe)
import GHC.Unit.Module.Graph
  ( ModuleGraphNode(..)
  , mgModSummaries' )
import Data.Maybe (mapMaybe)
import GHC.Unit.Types (UnitId)
import GHC.Data.Graph.Directed (flattenSCCs)
import qualified GHC.Utils.Exception as GHCEx
import GHC.Driver.Session
  ( DynFlags(..)
  , GeneralFlag(..)
  , GhcMode(..)
  , gopt_set
  , parseDynamicFlagsCmdLine
  , ModRenaming(..)
  , PackageArg(..)
  , PackageFlag(..)
  , WarningFlag(..)
  , wopt_unset
  )
import GHC.Utils.Exception (ExceptionMonad(..), handle)
import GHC.Driver.Backend (Backend(..))
import GHC
  ( GhcLink(..)
  , LoadHowMuch(..)
  , Phase(..)
  , ModLocation(..)
  , ModSummary(..)
  , Severity
  , SrcSpan
  , getModuleGraph
  , getSession
  , getSessionDynFlags
  , guessTarget
  , load
  , noLoc
  , parseModule
  , runGhcT
  , setSessionDynFlags
  , setTargets
  , topSortModuleGraph
  , typecheckModule
  , moduleNameString
  , moduleName
  )
import GHC.Paths (libdir)
import GHC.Driver.Monad
  ( GhcT(..)
  , liftIO
  , setSession )
import HaskellCodeExplorer.GhcUtils (isHsBoot,toText)
import HaskellCodeExplorer.ModuleInfo (ModuleDependencies, createModuleInfo)
import qualified HaskellCodeExplorer.Types as HCE
import GHC.Driver.Env
  ( hscEPS
  , hsc_HPT
  , hsc_logger)
import GHC.Utils.Outputable
  ( PprStyle
  , SDoc
  , neverQualify
  , showSDocUnsafe
  , ppr)
import GHC.Unit.State (initUnits)
import Prelude hiding (id)
import System.Directory
  ( doesFileExist
  , findExecutable
  , setCurrentDirectory
  , getCurrentDirectory
  , makeAbsolute
  , getDirectoryContents
  )
import qualified System.Directory.Tree as DT
import System.Exit (exitFailure)
import System.FilePath
  ( (</>)
  , addTrailingPathSeparator
  , isAbsolute
  , joinPath
  , normalise
  , replaceExtension
  , splitPath
  , takeExtension
  , takeFileName
  , takeBaseName
  , takeDirectory
  , splitDirectories
  )
import System.FilePath.Find (find,always,(==?),fileName)
import System.Process (readProcess)
import qualified Data.Set as Set
import Distribution.PackageDescription
import Distribution.PackageDescription.Configuration (flattenPackageDescription)
import Distribution.PackageDescription.Parsec (parseGenericPackageDescription, runParseResult)
import qualified Data.ByteString as BS
import Distribution.Verbosity (normal)
import Distribution.ModuleName (toFilePath)
import Distribution.Simple.Compiler (CompilerFlavor(..))
import Distribution.Pretty (prettyShow)
import Distribution.Utils.Path (getSymbolicPath)
import Distribution.PackageDescription (package)
import Distribution.Types.PackageId (pkgName, pkgVersion)
import Distribution.Pretty (prettyShow)
import Control.Monad.Catch (MonadCatch, MonadThrow, MonadMask, catch, throwM, mask)
import qualified Data.Version as BaseV
import qualified Distribution.Types.Version as CabalV

createPackageInfo ::
     FilePath
  -> Maybe FilePath
  -> HCE.SourceCodePreprocessing
  -> [String]
  -> [String]
  -> LoggingT IO (HCE.PackageInfo HCE.ModuleInfo)
createPackageInfo packageDirectoryPath mbDistDirRelativePath sourceCodePreprocessing additionalGhcOptions ignoreDirectories = do
  packageDirectoryAbsPath <- liftIO $ makeAbsolute packageDirectoryPath
  currentDirectory <- liftIO getCurrentDirectory
  liftIO $ setCurrentDirectory packageDirectoryAbsPath

  distDir <-
    case mbDistDirRelativePath of
      Just path -> pure (packageDirectoryAbsPath </> path)
      Nothing -> do
        eitherDistDir <- findDistDirectory packageDirectoryAbsPath
        case eitherDistDir of
          Right d -> pure d
          Left err -> logErrorN (T.pack err) >> liftIO exitFailure

  cabalFiles <-
    liftIO $
      length .
      filter (\p -> takeFileName p /= ".cabal" && takeExtension p == ".cabal")
      <$> getDirectoryContents packageDirectoryAbsPath
  _ <-
    if cabalFiles == 0
      then logErrorN (T.concat ["No .cabal file found in ", T.pack packageDirectoryAbsPath]) >> liftIO exitFailure
      else when (cabalFiles >= 2) $ do
             logErrorN (T.concat ["Found more than one .cabal file in ", T.pack packageDirectoryAbsPath])
             liftIO exitFailure

  cabalFile <- liftIO $ findSingleCabalFile packageDirectoryAbsPath
  bs <- liftIO $ BS.readFile cabalFile
  let (_warnings, res) = runParseResult (parseGenericPackageDescription bs)
  gpd <- case res of
    Right g -> pure g
    Left err -> do
      logErrorN (T.pack ("Failed to parse cabal file: " <> show err))
      liftIO exitFailure
  let pd   = flattenPackageDescription gpd
      pkgId = package pd
      currentPackageId =
        HCE.PackageId
          (T.pack (prettyShow (pkgName pkgId)))
          (makeVersion (CabalV.versionNumbers (pkgVersion pkgId)))
  logInfoN $ T.append "Indexing " $ HCE.packageIdToText currentPackageId

  let buildComponents :: [(HCE.ComponentId, [String], (Maybe FilePath, [String]), [FilePath], HCE.ComponentType)]
      buildComponents = libs pd ++ subLibs pd ++ flibs pd ++ exes pd ++ tests pd ++ benches pd

      libs Distribution.PackageDescription.PackageDescription{library = Just lib} =
        [ mkLib "lib" lib ]
      libs _ = []

      subLibs Distribution.PackageDescription.PackageDescription{subLibraries = xs} =
        [ mkLib ("sublib-" <> unUnqualComponentName uqn) l
        | l <- xs
        , LSubLibName uqn <- [libName l]
        ]

      flibs Distribution.PackageDescription.PackageDescription{foreignLibs = xs} =
        [ mkFLib ("flib-" <> unUnqualComponentName (foreignLibName f)) f | f <- xs ]

      exes Distribution.PackageDescription.PackageDescription{executables = xs} =
        [ mkExe ("exe-" <> unUnqualComponentName (exeName e)) e | e <- xs ]

      tests Distribution.PackageDescription.PackageDescription{testSuites = xs} =
        [ mkTest ("test-" <> unUnqualComponentName (testName t)) t | t <- xs ]

      benches Distribution.PackageDescription.PackageDescription{benchmarks = xs} =
        [ mkBench ("bench-" <> unUnqualComponentName (benchmarkName b)) b | b <- xs ]

      -- helpers

      mkLib cid lib =
        let bi        = libBuildInfo lib
            srcDirs   = collectHsDirs distDir bi
            exposeds  = map Distribution.Pretty.prettyShow (exposedModules lib)
            others    = map Distribution.Pretty.prettyShow (otherModules bi)
            sigs      = map Distribution.Pretty.prettyShow (signatures lib)
            mods      = exposeds ++ others ++ sigs
        in ( HCE.ComponentId (T.pack cid)
           , ghcOptionsForBI packageDirectoryAbsPath distDir bi
           , (Nothing, mods)
           , srcDirs
           , HCE.Lib
           )

      mkFLib cid fl =
        let bi      = foreignLibBuildInfo fl
            srcDirs = collectHsDirs distDir bi
        in ( HCE.ComponentId (T.pack cid)
           , ghcOptionsForBI packageDirectoryAbsPath distDir bi
           , (Nothing, [])
           , srcDirs
           , HCE.FLib (T.pack (unUnqualComponentName (foreignLibName fl)))
           )

      mkExe cid e =
        let bi      = (buildInfo e)
            srcDirs = collectHsDirs distDir bi
            mainFP  = modulePath e
        in ( HCE.ComponentId (T.pack cid)
           , ghcOptionsForBI packageDirectoryAbsPath distDir bi
           , (Just mainFP, [])
           , srcDirs
           , HCE.Exe (T.pack (unUnqualComponentName (exeName e)))
           )

      mkTest cid t =
        case testInterface t of
          TestSuiteExeV10 _ mainFP ->
            let bi      = testBuildInfo t
                srcDirs = collectHsDirs distDir bi
            in ( HCE.ComponentId (T.pack cid)
               , ghcOptionsForBI packageDirectoryAbsPath distDir bi
               , (Just mainFP, [])
               , srcDirs
               , HCE.Test (T.pack (unUnqualComponentName (testName t)))
               )
          _ ->
            let bi = testBuildInfo t
            in ( HCE.ComponentId (T.pack cid)
               , ghcOptionsForBI packageDirectoryAbsPath distDir bi
               , (Nothing, [])
               , collectHsDirs distDir bi
               , HCE.Test (T.pack (unUnqualComponentName (testName t)))
               )

      mkBench cid b =
        case benchmarkInterface b of
          BenchmarkExeV10 _ mainFP ->
            let bi      = benchmarkBuildInfo b
                srcDirs = collectHsDirs distDir bi
            in ( HCE.ComponentId (T.pack cid)
               , ghcOptionsForBI packageDirectoryAbsPath distDir bi
               , (Just mainFP, [])
               , srcDirs
               , HCE.Bench (T.pack (unUnqualComponentName (benchmarkName b)))
               )
          _ ->
            let bi = benchmarkBuildInfo b
            in ( HCE.ComponentId (T.pack cid)
               , ghcOptionsForBI packageDirectoryAbsPath distDir bi
               , (Nothing, [])
               , collectHsDirs distDir bi
               , HCE.Bench (T.pack (unUnqualComponentName (benchmarkName b)))
               )

      unUnqualComponentName = Distribution.Pretty.prettyShow

      libSrcDirs =
        concatMap (\(_,_,_,dirs,_) -> dirs)
          $ filter (\(_,_,_,_,ct) -> HCE.isLibrary ct) buildComponents
  
  (indexedModules, (_fileMapResult, _defSiteMapResult, modNameMapResult)) <-
    foldM
      (\(modules, (fileMap, defSiteMap, modNameMap))
         (compId, options, (mbMain, moduleNames), srcDirs, _compType) -> do
           mbMainPath <-
             case mbMain of
               Just mainPath ->
                 liftIO $
                   findM doesFileExist
                     (mainPath : map (\d -> normalise (d </> mainPath)) srcDirs)
               Nothing -> pure Nothing
           (modules', (fileMap', defSiteMap', modNameMap')) <-
             indexBuildComponent
               sourceCodePreprocessing
               currentPackageId
               compId
               (fileMap, defSiteMap, modNameMap)
               srcDirs
               libSrcDirs
               (options ++ additionalGhcOptions)
               (maybe moduleNames (: moduleNames) mbMainPath)
           pure (modules ++ modules', (fileMap', defSiteMap', modNameMap')))
      ([], (HM.empty, HM.empty, HM.empty))
      buildComponents

  let moduleMap =
        HM.fromList $ map (\m -> (m.id, m)) indexedModules
      references =
        L.foldl' addReferencesFromModule HM.empty indexedModules
      topLevelIdentifiersTrie =
        L.foldl' addTopLevelIdentifiersFromModule HCE.emptyTrie
        $ L.filter (not . isHsBoot . (\m -> m.id)) indexedModules

  directoryTree <-
    liftIO $
      buildDirectoryTree
        packageDirectoryAbsPath
        ignoreDirectories
        (\p -> HM.member (HCE.HaskellModulePath . T.pack $ p) moduleMap)

  liftIO $ setCurrentDirectory currentDirectory
  pure HCE.PackageInfo
        { id = currentPackageId
        , moduleMap = moduleMap
        , moduleNameMap = modNameMapResult
        , directoryTree = directoryTree
        , externalIdOccMap = references
        , externalIdInfoMap = topLevelIdentifiersTrie
        }
  where
    ghcOptionsForBI :: FilePath -> FilePath -> BuildInfo -> [String]
    ghcOptionsForBI pkgDir distDir bi =
         hcOptions GHC bi
      ++ langOpts
      ++ extOpts
      ++ includeOpts
      ++ srcDirOpts
      where
        langOpts =
          maybe [] (\l -> ["-X" <> Distribution.Pretty.prettyShow l]) (defaultLanguage bi)
        extOpts =
          let exts = map Distribution.Pretty.prettyShow (defaultExtensions bi ++ otherExtensions bi)
          in map ("-X" <>) exts
        includeOpts =
          concat
            [ concatMap (\d -> ["-I" <> absJoin d]) (includeDirs bi)
            , cppOptions bi
            ]
        srcDirOpts =
          concatMap (\d -> ["-i" <> absJoin d]) (collectHsDirs distDir bi)
        absJoin d =
          if isAbsolute d then d else normalise (pkgDir </> d)

    collectHsDirs :: FilePath -> BuildInfo -> [FilePath]
    collectHsDirs distDir bi =
      let sourceDirs = map getSymbolicPath (hsSourceDirs bi)
          autogenDir = distDir <> "/build/autogen"
       in sourceDirs <> [ autogenDir ]

findSingleCabalFile :: FilePath -> IO FilePath
findSingleCabalFile dir = do
  xs <- filter (\p -> takeExtension p == ".cabal") <$> getDirectoryContents dir
  case xs of
    [x] -> pure (dir </> x)
    []  -> ioError (userError ("No .cabal file found in " <> dir))
    _   -> ioError (userError ("Multiple .cabal files in " <> dir))

ghcVersion :: Version
ghcVersion = makeVersion [9, 10, 2, 0]

buildDirectoryTree :: FilePath -> [FilePath] -> (FilePath -> Bool) -> IO HCE.DirTree
buildDirectoryTree path ignoreDirectories isHaskellModule = do
  (_dir DT.:/ tree) <- DT.readDirectoryWith (const . return $ ()) path
  -- Tuple up the complete file path with the file contents, by building up the path,
  -- trie-style, from the root. The filepath will be relative to "anchored" directory.
  let treeWithPaths = DT.zipPaths ("" DT.:/ DT.filterDir (not . ignore) tree)
  return $ toDirTree (removeTopDir . fst <$> treeWithPaths)
  where
    ignore :: DT.DirTree a -> Bool
    ignore (DT.Dir dirName _)
      | "." `L.isPrefixOf` dirName = True
      | dirName == "dist" = True
      | dirName == "dist-newstyle" = True
      | dirName == "tmp" = True
      | otherwise = dirName `elem` ignoreDirectories
    ignore (DT.Failed _ _) = True
    ignore _ = False
    removeTopDir :: FilePath -> FilePath
    removeTopDir p =
      case splitPath p of
        _x:xs -> joinPath xs
        [] -> ""
    toDirTree :: DT.DirTree FilePath -> HCE.DirTree
    toDirTree (DT.Dir name contents) =
      HCE.Dir name (map toDirTree . filter (not . DT.failed) $ contents)
    toDirTree (DT.File name filePath) =
      HCE.File name filePath (isHaskellModule filePath)
    toDirTree (DT.Failed name err) =
      HCE.File (name ++ " : " ++ show err) "" False

addTopLevelIdentifiersFromModule ::
     HCE.Trie Char HCE.ExternalIdentifierInfo
  -> HCE.ModuleInfo
  -> HCE.Trie Char HCE.ExternalIdentifierInfo
addTopLevelIdentifiersFromModule trieIdInfo HCE.ModuleInfo {..} =
  L.foldl'
    (\trie idInfo@(HCE.ExternalIdentifierInfo HCE.IdentifierInfo {..}) ->
       HCE.insertToTrie S.insert (T.unpack demangledOccName) idInfo trie)
    trieIdInfo
    externalIds

addReferencesFromModule ::
     HM.HashMap HCE.ExternalId (S.Set HCE.IdentifierSrcSpan)
  -> HCE.ModuleInfo
  -> HM.HashMap HCE.ExternalId (S.Set HCE.IdentifierSrcSpan)
addReferencesFromModule references modInfo@HCE.ModuleInfo {..} =
  eachIdentifierOccurrence
    references
    modInfo
    (\occMap lineNumber startCol endCol occ ->
       let mbIdExternalId =
             HCE.externalId =<<
             maybe
               Nothing
               (`HM.lookup` idInfoMap)
               occ.internalId
           idSrcSpan =
             HCE.IdentifierSrcSpan
               { modulePath = id
               , line = lineNumber
               , startColumn = startCol
               , endColumn = endCol
               }
        in case mbIdExternalId of
             Just externalId ->
               HM.insertWith S.union externalId (S.singleton idSrcSpan) occMap
             Nothing -> occMap)

findDistDirectory :: FilePath -> LoggingT IO (Either String FilePath)
findDistDirectory packagePath = do
  let parents =
        reverse . map joinPath . filter (not . null) . L.inits . splitPath $
        packagePath
  -- e.g., ["/dir/subdir/subsubdir","/dir/subdir/","/dir/","/"]
  hasStackYaml <-
    liftIO $ anyM (\path -> doesFileExist (path </> "stack.yaml")) parents
  mbStackExecutable <- liftIO $ findExecutable "stack"
  case (hasStackYaml, mbStackExecutable) of
    (True, Just stack) -> do
      let removeEndOfLine str
            | null str = str
            | otherwise = init str
      logInfoN
        "Found stack.yaml. Executing \"stack path --dist-dir\" to get dist directory."
      eitherDistDir :: (Either IOException String) <-
        liftIO .
        try . fmap removeEndOfLine . readProcess stack ["path", "--dist-dir"] $
        ""
      case eitherDistDir of
        Right distDir -> do
          logInfoN $ T.append "Stack dist directory : " $ T.pack distDir
          hasSetupConfig <- liftIO $ doesFileExist $ distDir </> "setup-config"
          if hasSetupConfig
            then return $ Right distDir
            else return $
                 Left
                   "Cannot find setup-config file in a dist directory. Has the package been built?"
        Left exception ->
          return $
          Left $
          "Error while executing \"stack path --dist-dir\" : " ++ show exception
    _ -> do
      logInfoN "Trying to find dist directory"
      setupConfigPaths <-
        liftIO $
        map (takeDirectory . normalise) <$>
        find always (fileName ==? "setup-config") "."
      case setupConfigPaths of
        [] ->
          return $
          Left "Cannot find dist directory. Has the package been built?"
        [path] -> do
          logInfoN $ T.append "Found dist directory : " $ T.pack path
          return $ Right path
        _ ->
          return $
          Left $
          "Found multiple possible dist directories : \n" ++
          show setupConfigPaths ++ " \nPlease specify --dist option"

eachIdentifierOccurrence ::
     forall a.
     a
  -> HCE.ModuleInfo
  -> (a -> IM.Key -> Int -> Int -> HCE.IdentifierOccurrence -> a)
  -> a
eachIdentifierOccurrence accumulator HCE.ModuleInfo {..} f =
  IM.foldlWithKey'
    (\acc lineNumber occurences ->
       L.foldl'
         (\a ((startCol, endCol), occ) -> f a lineNumber startCol endCol occ)
         acc
         occurences)
    accumulator
    idOccMap

instance MonadLoggerIO (GhcT (LoggingT IO)) where
  askLoggerIO = GhcT $ const askLoggerIO

instance MonadLogger (GhcT (LoggingT IO)) where
  monadLoggerLog loc source level =
    GhcT . const . monadLoggerLog loc source level

gtrySync :: (ExceptionMonad m) => m a -> m (Either SomeException a)
gtrySync action = ghandleSync (return . Left) (fmap Right action)

ghandleSync :: ExceptionMonad m => (SomeException -> m a) -> m a -> m a
ghandleSync onError action =
  catch action $ \ex ->
    case fromException ex of
      Just (asyncEx :: SomeAsyncException) -> throwM asyncEx
      _                                    -> onError ex

indexBuildComponent ::
     HCE.SourceCodePreprocessing -- ^ Before or after preprocessor
  -> HCE.PackageId -- ^ Current package id
  -> HCE.ComponentId -- ^ Current component id
  -> ModuleDependencies -- ^ Already indexed modules
  -> [FilePath] -- ^ Src dirs
  -> [FilePath] -- ^ Src dirs of libraries
  -> [String] -- ^ Command-line options for GHC
  -> [String] -- ^ Modules to compile
  -> LoggingT IO ([HCE.ModuleInfo],ModuleDependencies)
indexBuildComponent sourceCodePreprocessing currentPackageId componentId deps@(fileMap, defSiteMap, modNameMap) srcDirs libSrcDirs options modules = do
  let onError ex = do
        logErrorN $
          T.concat
            [ "Error while indexing component "
            , HCE.getComponentId componentId
            , " : "
            , T.pack . show $ ex
            ]
        return ([], deps)
  logDebugN $ T.pack $ "------------------------------------------------------------------------"
  logDebugN $ T.pack $ "indexBuildComponent"
  ghandleSync onError $
    runGhcT (Just libdir) $ do
      logDebugN $ (T.append "Component id : " $ HCE.getComponentId componentId)
      logDebugN $ (T.append "Modules : " $ T.pack $ show modules)
      logDebugN $ (T.append "srcDirs : " $ T.pack $ show srcDirs)
      logDebugN $
        (T.append "GHC command line options : " $
         T.pack $ L.unwords (options ++ modules))
      flags <- getSessionDynFlags
      (flags', _, _) <-
        parseDynamicFlagsCmdLine
          flags
          (L.map noLoc . L.filter ("-Werror" /=) $ options) -- -Werror flag makes warnings fatal
      logFn <- askLoggerIO
      let logAction :: LogFlags -> MessageClass -> SrcSpan -> SDoc -> IO ()
          logAction _ msgClass srcSpan msg =
            runLoggingT
              (logDebugN $
                T.append "GHC message : " $
                T.pack $
                  showSDocUnsafe msg ++
                  " , MessageClass: " ++
                  " , SrcSpan : " ++ show srcSpan)
              logFn
          mbTmpDir =
            case hiDir flags' of
              Just buildDir ->
                Just $ buildDir </> (takeBaseName buildDir ++ "-tmp")
              Nothing -> Nothing
          baseFlags = (flags'
            { ghcLink = LinkInMemory
            , ghcMode = CompManager
            , importPaths = importPaths flags' ++ maybeToList mbTmpDir
            , packageFlags = [ExposePackage "-package ghc"
                (PackageArg "ghc")
                (ModRenaming True [])]
            })
          optFlags = L.foldl' gopt_set baseFlags [Opt_Haddock, Opt_ExternalInterpreter]
          noWarnFlags = L.foldl' wopt_unset optFlags [minBound .. maxBound :: WarningFlag]
      _ <- setSessionDynFlags noWarnFlags
      targets <- mapM (\m -> guessTarget m (Nothing :: Maybe UnitId) (Nothing :: Maybe Phase)) modules
      logDebugN $ T.pack $ "setTarget : " <> (showSDocUnsafe $ ppr targets)
      setTargets targets
      logDebugN "load LoadAllTargets"
      _ <- load LoadAllTargets
      logDebugN "getModuleGraph"
      modGraph <- getModuleGraph
      let topSortNodes = flattenSCCs (topSortModuleGraph False modGraph Nothing)
          toModSummary :: ModuleGraphNode -> Maybe ModSummary
          toModSummary (ModuleNode _ ms) = Just ms
          toModSummary _               = Nothing
          topSortMods = mapMaybe toModSummary topSortNodes
          buildDir =
            addTrailingPathSeparator . normalise . fromMaybe "" . hiDir $
            flags'
          pathsModuleName =
            "Paths_" ++
            map
              (\c ->
                 if c == '-'
                   then '_'
                   else c)
              (T.unpack currentPackageId.name)
      (modSumWithPath, modulesNotFound) <-
        (\(mods, notFound) ->
           ( L.reverse .
             L.foldl'
               (\acc (mbPath, modSum) ->
                  case mbPath of
                    Just path
                      | not $ HM.member path defSiteMap -> (path, modSum) : acc
                    _ -> acc)
               [] $
             mods
           , map snd notFound)) .
        L.partition (\(mbPath, _) -> isJust mbPath) <$>
        mapM
          (\modSum ->
             liftIO $
             (, modSum) <$>
             findHaskellModulePath buildDir (srcDirs ++ libSrcDirs) modSum)
          (filter
             (\modSum ->
                pathsModuleName /=
                (moduleNameString . moduleName $ ms_mod modSum))
             topSortMods)
      unless (null modulesNotFound) $
        logErrorN $
        T.append
          "Cannot find module path : "
          (toText (map ms_mod modulesNotFound))
      foldM
        (\(indexedModules, (fileMap', defSiteMap', modNameMap')) (modulePath, modSum) -> do
           result <-
             indexModule
               sourceCodePreprocessing
               componentId
               currentPackageId
               flags'
               (fileMap', defSiteMap', modNameMap')
               (modulePath, modSum)
           case result of
             Right (modInfo, (fileMap'', defSiteMap'', modNameMap'')) ->
               return
                 ( modInfo : indexedModules
                 , (fileMap'', defSiteMap'', modNameMap''))
             Left exception -> do
               logErrorN $
                 T.concat
                   [ "Error while indexing "
                   , T.pack . show $ modulePath
                   , " : "
                   , T.pack . show $ exception
                   ]
               return (indexedModules, (fileMap', defSiteMap', modNameMap')))
        ([], (fileMap, defSiteMap, modNameMap))
        modSumWithPath

findHaskellModulePath ::
     FilePath -> [FilePath] -> ModSummary -> IO (Maybe HCE.HaskellModulePath)
findHaskellModulePath buildDir srcDirs modSum = do
  case normalise <$> (ml_hs_file . ms_location $ modSum) of
    Just modulePath -> do
      let toHaskellModulePath = return . Just . HCE.HaskellModulePath . T.pack
          removeTmpDir path =
            case splitDirectories path of
              parent:rest ->
                if "-tmp" `L.isSuffixOf` parent
                  then joinPath rest
                  else path
              _ -> path
       in case removeTmpDir <$> L.stripPrefix buildDir modulePath of
            -- File is in the build directory
            Just path
              | takeExtension path == ".hs-boot" -> do
                let possiblePaths = path : map (</> path) srcDirs
                mbFoundPath <- findM doesFileExist possiblePaths
                case mbFoundPath of
                  Just p -> toHaskellModulePath p
                  _ -> return Nothing
              | takeExtension path == ".hs" -> do
                let paths =
                      map
                        (replaceExtension path)
                        HCE.haskellPreprocessorExtensions
                    possiblePaths =
                      paths ++
                      concatMap (\srcDir -> map (srcDir </>) paths) srcDirs
                mbFoundPath <- findM doesFileExist possiblePaths
                case mbFoundPath of
                  Just p -> toHaskellModulePath p
                  _ -> return Nothing
              | otherwise -> do
                return Nothing
            Nothing -> do
              toHaskellModulePath modulePath
    Nothing -> do
      return Nothing

indexModule ::
     HCE.SourceCodePreprocessing
  -> HCE.ComponentId
  -> HCE.PackageId
  -> DynFlags
  -> ModuleDependencies
  -> (HCE.HaskellModulePath, ModSummary)
  -> GhcT (LoggingT IO) (Either SomeException ( HCE.ModuleInfo
                                              , ModuleDependencies))
indexModule sourceCodePreprocessing componentId currentPackageId flags deps (modulePath, modSum) =
  gtrySync $ do
    logInfoN (T.append "Indexing " $ HCE.getHaskellModulePath modulePath)
    parsedModule <- parseModule modSum
    typecheckedModule <- typecheckModule parsedModule -- If module has import error. here will throw exception
    hscEnv <- getSession
    externalPackageState <- liftIO (hscEPS hscEnv)
    originalSourceCode <-
      liftIO $
      T.replace "\t" "        " . TE.decodeUtf8 <$>
      BS.readFile (T.unpack . HCE.getHaskellModulePath $ modulePath)
    let (modInfo, (fileMap', exportMap', moduleNameMap'), typeErrors) =
          createModuleInfo
            deps
            ( flags
            , typecheckedModule
            , hsc_HPT hscEnv
            , externalPackageState
            , modSum)
            modulePath
            currentPackageId
            componentId
            (originalSourceCode, sourceCodePreprocessing)
            hscEnv
    unless (null typeErrors) $
      logInfoN $ T.append "Type errors : " $ T.pack $ show typeErrors
    deepseq modInfo $ return (modInfo, (fileMap', exportMap', moduleNameMap'))
