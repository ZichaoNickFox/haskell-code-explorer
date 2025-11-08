{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}

module HaskellCodeExplorer.ModuleInfo
  ( createModuleInfo
  , ModuleDependencies
  ) where

import qualified Data.Generics.Uniplate.Data as U
import GHC.Unit.State (UnitState)
import Control.Monad.State.Strict (execState,evalState,get,put,State)
import qualified Data.Aeson as Aeson
import Data.Aeson.Text(encodeToLazyText)
import qualified Data.Vector as V
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.IntervalMap.Strict as IVM
import           GHC.Hs.Binds (HsBindLR, LHsBindLR)
import qualified Data.List as L hiding (span)
import Data.Maybe (fromMaybe, mapMaybe)
import GHC.Hs.Extension (GhcRn)
import GHC.Types.SrcLoc
  ( SrcSpan(..)      -- 关键：带入 RealSrcSpan/UnhelpfulSpan 构造子
  , RealSrcSpan
  , srcSpanStartLine
  , srcSpanStartCol
  )
import qualified Data.Set as S
import           GHC.Hs.Utils (collectHsBindBinders, CollectFlag(..))
import qualified Data.Text as T
import GHC.Driver.Env(hsc_unit_env, HscEnv)
import GHC.Unit.Env (ue_units)
import qualified Data.Text.Encoding as TE
import           GHC.Types.Unique.DFM           ( eltsUDFM )
import Data.Text.Lazy (toStrict)
import Documentation.Haddock.Types (DocH)
import GHC.Driver.Session
  ( DynFlags
  , targetPlatform )
import GHC
  ( GenLocated(..)
  , ModSummary
  , locA
  , getLocA
  , ModuleInfo
  , ModuleName
  , SrcSpan
  , TyThing(..)
  , Type
  , TypecheckedModule
  , getLoc
  , isGoodSrcSpan
  , modInfoExportsWithSelectors
  , modInfoInstances
  , moduleInfo
  , moduleNameString
  , ms_hspp_buf
  , ms_mod
  , renamedSource
  , tm_internals_
  , tm_typechecked_source
  , unLoc
  )
import GHC.Core.Type(expandTypeSynonyms)
import GHC.Core.TyCon (isFamInstTyCon,tyConName)
import HaskellCodeExplorer.AST.RenamedSource
import HaskellCodeExplorer.AST.TypecheckedSource
import HaskellCodeExplorer.GhcUtils
import HaskellCodeExplorer.Preprocessor (createSourceCodeTransformation)
import qualified HaskellCodeExplorer.Types as HCE
import GHC.Hs.Binds (HsBindLR)
import GHC.Hs.Decls
  ( ForeignDecl(..)
  , HsDecl(..)
  , LForeignDecl(..)
  , LInstDecl(..)
  , LTyClDecl(..)
  , LHsDecl
  , HsGroup(..)
  , InstDecl
  , TyClDecl
  , InstDecl(..)
  , group_tyclds
  , tyClDeclLName
  , tcdName
  , hsGroupInstDecls
  )
import GHC.Hs.Doc
  ( HsDocString
  , LHsDoc(..)
  , WithHsDocIdentifiers(..) )
import GHC.Hs.ImpExp (IE(..), ImportDecl(..), ideclImplicit)
import GHC.Hs.Utils(collectHsBindBinders)
import GHC.Unit.External
  ( ExternalPackageState
  , eps_PTE
  , eps_inst_env)
import GHC.Unit.Home.ModInfo
  ( HomePackageTable
  , hm_details)
import GHC.Unit.Module.ModDetails
  ( md_types )
import GHC.Types.TypeEnv
  ( TypeEnv
  , mkTypeEnv
  , typeEnvElts )
import GHC.Core.InstEnv (InstEnvs(..), is_dfun)
import GHC.Unit.Module(Module(..), moduleName)
import GHC.Types.Name (Name, OccName, getSrcSpan, nameOccName, nameSrcSpan, nameUnique)
import Prelude hiding(id,span)
import GHC.Types.Name.Reader(GlobalRdrEnv)
import GHC.Types.SrcLoc (isOneLineSpan, RealSrcSpan(..), srcSpanStartLine, srcSpanStartCol)
import GHC.Tc.Types (tcVisibleOrphanMods, tcg_inst_env, tcg_rdr_env, tcg_type_env)
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A
import GHC.Types.Unique (getKey)
import GHC.Types.Var (varName, varType,Id)
import GHC.Types.Var.Env (emptyTidyEnv)

type ModuleDependencies
   = ( HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
     , HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
     , HM.HashMap HCE.HaskellModuleName (HM.HashMap HCE.ComponentId HCE.HaskellModulePath))

type ModuleGhcData
   = ( DynFlags
     , TypecheckedModule
     , HomePackageTable
     , ExternalPackageState
     , ModSummary)

createModuleInfo ::
  ModuleDependencies -- ^ Modules that have already been indexed
  -> ModuleGhcData -- ^ Data types from GHC
  -> HCE.HaskellModulePath -- ^ Current module path
  -> HCE.PackageId -- ^ Current package id
  -> HCE.ComponentId -- ^ Current build component id
  -> (T.Text, HCE.SourceCodePreprocessing) -- ^ Source code
  -> HscEnv
  -> (HCE.ModuleInfo, ModuleDependencies, [TypeError])
createModuleInfo (fileMap, defSiteMap, moduleNameMap) (flags, typecheckedModule, homePackageTable, externalPackageState, modSum) modulePath currentPackageId compId (originalSourceCode, sourceCodePreprocessing) hscEnv=
  let globalRdrEnv = tcg_rdr_env . fst . tm_internals_ $ typecheckedModule
      modInfo = moduleInfo typecheckedModule
      (Just (hsGroup, _, _, _, _)) = renamedSource typecheckedModule
      exportedNamesSet = S.fromList $ modInfoExportsWithSelectors modInfo
      --------------------------------------------------------------------------------
      -- Preprocessed source
      --------------------------------------------------------------------------------
      (transformation, sourceCode') =
        prepareSourceCode
          sourceCodePreprocessing
          originalSourceCode
          modSum
          modulePath
      includedFiles = HM.keys $ HCE.fileIndex transformation
      --------------------------------------------------------------------------------
      -- Type environment
      --------------------------------------------------------------------------------
      (tcGblEnv, _) = tm_internals_ typecheckedModule
      currentModuleTyThings = typeEnvElts $ tcg_type_env tcGblEnv
      homePackageTyThings =
        concatMap (typeEnvElts . md_types . hm_details) $
        eltsUDFM homePackageTable
      externalPackagesTyThings = typeEnvElts $ eps_PTE externalPackageState
      typeEnv =
        mkTypeEnv
          (currentModuleTyThings ++
           homePackageTyThings ++ externalPackagesTyThings)
      --------------------------------------------------------------------------------
      -- Exported entities
      --------------------------------------------------------------------------------
      dataFamTyCons =
        mapMaybe
          (\case
             ATyCon tc
               | isFamInstTyCon tc -> Just $ tyConName tc
             _ -> Nothing)
          currentModuleTyThings
      (defSites, allNames) =
        createDefinitionSiteMap
          unitState
          flags
          currentPackageId
          compId
          defSiteMap
          fileMap
          globalRdrEnv
          transformation
          modInfo
          dataFamTyCons
          hsGroup
      --------------------------------------------------------------------------------
      -- Instance environment
      --------------------------------------------------------------------------------
      homeInstEnv = tcg_inst_env tcGblEnv
      visOrphanModules = tcVisibleOrphanMods tcGblEnv
      packageInstEnv = eps_inst_env externalPackageState
      instEnv = InstEnvs packageInstEnv homeInstEnv visOrphanModules
      --------------------------------------------------------------------------------
      declarations =
        createDeclarations flags hsGroup typeEnv exportedNamesSet transformation
      unitState = ue_units (hsc_unit_env hscEnv)
      environment =
        Environment
          { envDynFlags = flags
          , envInstEnv = instEnv
          , envTypeEnv = typeEnv
          , envTransformation = transformation
          , envCurrentModuleDefSites = defSites
          , envFileMap = fileMap
          , envDefSiteMap = defSiteMap
          , envModuleNameMap = moduleNameMap
          , envPackageId = currentPackageId
          , envComponentId = compId
          , envExportedNames = exportedNamesSet
          , envUnitState = unitState
          }
      externalIds =
        L.foldl'
          (\acc name ->
             maybe
               acc
               (\id -> (HCE.ExternalIdentifierInfo $ mkIdentifierInfo environment id (Just name)) : acc)
               (lookupIdInTypeEnv typeEnv name))
          []
          allNames
      currentModuleName =
        HCE.HaskellModuleName . T.pack
        . moduleNameString . moduleName . ms_mod
        $ modSum
      -- currentModuleName =
      --   (\(Module _ name) ->
      --      HCE.HaskellModuleName . T.pack . moduleNameString $ name) .
      --   ms_mod $
      --   modSum
      SourceInfo {..} = foldAST unitState environment typecheckedModule
   in (tidyInternalIds HCE.ModuleInfo
          { id = modulePath
          , transformation = transformation
          , name = currentModuleName
          , declarations = declarations
          , exprInfoMap = sourceInfoExprMap
          , idInfoMap = sourceInfoIdMap
          , idOccMap = sourceInfoIdOccMap
          , definitionSiteMap = defSites
          , source = V.fromList . T.splitOn "\n" $ sourceCode'
          , externalIds = externalIds
          }
      , if not $ isHsBoot modulePath
          then ( HM.union
                   (HM.fromList .
                    (( HCE.HaskellFilePath $ HCE.getHaskellModulePath modulePath
                     , modulePath) :) .
                    map (, modulePath) $
                    includedFiles)
                   fileMap
               , HM.union (HM.singleton modulePath defSites) defSiteMap
               , HM.insertWith HM.union currentModuleName
                   (HM.singleton compId modulePath) moduleNameMap)
          else (fileMap, defSiteMap, moduleNameMap)
       , sourceInfoTypeErrors)

data SourceInfo = SourceInfo
  { sourceInfoExprMap :: HCE.ExpressionInfoMap
  , sourceInfoIdMap :: HCE.IdentifierInfoMap
  , sourceInfoIdOccMap :: HCE.IdentifierOccurrenceMap
  , sourceInfoTypeErrors :: [TypeError]
  } deriving (Show, Eq)

tidyInternalIds :: HCE.ModuleInfo -> HCE.ModuleInfo
tidyInternalIds modInfo = evalState (U.transformBiM tidy modInfo) (HM.empty, 0)
  where
    tidy ::
         HCE.InternalId -> State (HM.HashMap T.Text T.Text, Int) HCE.InternalId
    tidy (HCE.InternalId text) = do
      (hmap, number) <- get
      case HM.lookup text hmap of
        Just val -> return $ HCE.InternalId val
        Nothing -> do
          let nextInternalId = T.pack . show $ number
          put (HM.insert text nextInternalId hmap, number + 1)
          return $ HCE.InternalId nextInternalId

prepareSourceCode ::
     HCE.SourceCodePreprocessing
  -> T.Text
  -> ModSummary
  -> HCE.HaskellModulePath
  -> (HCE.SourceCodeTransformation, T.Text)
prepareSourceCode sourceCodePreprocessing originalSourceCode modSum modulePath =
  let sourceCodeAfterPreprocessing =
        case TE.decodeUtf8' $
             maybe
               (error "ms_hspp_buf is Nothing")
               stringBufferToByteString
               (ms_hspp_buf modSum) of
          Right text -> T.replace "\t" "        " text
          Left err ->
            error $
            "decodeUtf8' : " ++ show err ++ " , file : " ++ show modulePath
   in case sourceCodePreprocessing of
        HCE.BeforePreprocessing ->
          let sourceCodeLines = T.splitOn "\n" originalSourceCode
           in ( HCE.SourceCodeTransformation
                  (length sourceCodeLines)
                  modulePath
                  S.empty
                  HM.empty
              , originalSourceCode)
        HCE.AfterPreprocessing ->
          createSourceCodeTransformation
            modulePath
            originalSourceCode
            sourceCodeAfterPreprocessing

createDefinitionSiteMap ::
  UnitState
  -> DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
  -> HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
  -> GlobalRdrEnv
  -> HCE.SourceCodeTransformation
  -> ModuleInfo
  -> [Name]
  -> HsGroup GhcRn
  -> (HCE.DefinitionSiteMap, [Name])
createDefinitionSiteMap unitState flags currentPackageId compId defSiteMap fileMap globalRdrEnv transformation modInfo dataFamTyCons hsGroup =
  let
      --------------------------------------------------------------------------------
      -- Collect declarations
      --------------------------------------------------------------------------------
      allDecls :: [LHsDecl GhcRn]
      allDecls =
        L.sortOn
          (\d -> case locA (getLocA d) of
                  RealSrcSpan r _ -> (srcSpanStartLine r, srcSpanStartCol r)
                  _               -> (maxBound :: Int, maxBound :: Int))
          (ungroup hsGroup)

      (instanceDeclsWithDocs, valueAndTypeDeclsWithDocs) =
        L.partition
          (\(L _ decl, _) ->
             case decl of
               InstD {} -> True
               _        -> False)
          (collectDocs allDecls)

      --------------------------------------------------------------------------------
      -- Instances
      --------------------------------------------------------------------------------
      instanceDocMap :: M.Map RealSrcSpan [LHsDoc GhcRn]
      instanceDocMap =
        M.fromList $
          mapMaybe
            (\(L nSpan decl, docs) ->
              case decl of
                InstD _ (ClsInstD _ _inst) ->
                  case locA nSpan of
                    RealSrcSpan r _ -> Just (r, docs)
                    _               -> Nothing
                _ -> Nothing)
            instanceDeclsWithDocs

      nameLocation :: Maybe SrcSpan -> Name -> HCE.LocationInfo
      nameLocation mbSrcSpan name =
        nameLocationInfo
          unitState
          flags
          currentPackageId
          compId
          transformation
          fileMap
          defSiteMap
          Nothing
          Nothing
          name

      docHToHtml :: DocH (ModuleName, OccName) Name -> HCE.HTML
      docHToHtml =
        docWithNamesToHtml
          unitState
          flags
          currentPackageId
          compId
          transformation
          fileMap
          defSiteMap

      instancesWithDocumentation =
        HM.fromList $
          map
            (\clsInst ->
               ( instanceToText flags clsInst
               , let location = nameLocation Nothing (varName . is_dfun $ clsInst)
                  in case getSrcSpan clsInst of
                        RealSrcSpan r _ ->
                          case M.lookup r instanceDocMap of
                            Just hsDocs ->
                              let hsDocStrings = [ s | L _ (WithHsDocIdentifiers s _) <- hsDocs ]
                                  doc         = hsDocsToDocH unitState flags globalRdrEnv hsDocStrings
                              in HCE.DefinitionSite location (Just (docHToHtml doc))
                            Nothing -> HCE.DefinitionSite location Nothing
                        _ -> HCE.DefinitionSite location Nothing
                        ))
            (modInfoInstances modInfo)

      --------------------------------------------------------------------------------
      -- Values and types
      --------------------------------------------------------------------------------
      mainDeclNamesWithDocumentation =
        concatMap
          (\(L spanA decl, docs) -> map (, docs, locA spanA) $ getMainDeclBinder decl)
          valueAndTypeDeclsWithDocs

      dataFamTyConsWithoutDocs =
        map (\name -> (name, [], nameSrcSpan name)) dataFamTyCons

      allDeclsSrc :: [GenLocated SrcSpan (HsDecl GhcRn)]
      allDeclsSrc = map (\(L la d) -> L (locA la) d) allDecls

      allNamesWithDocumentation =
        mainDeclNamesWithDocumentation
          ++ subordinateNamesWithDocs allDeclsSrc
          ++ dataFamTyConsWithoutDocs

      (valuesWithDocumentation, typesWithDocumentation) =
        L.partition
          (\(name, _, _) ->
             case occNameNameSpace . nameOccName $ name of
               HCE.VarName  -> True
               HCE.DataName -> True
               _            -> False)
          allNamesWithDocumentation

      toHashMap ::
           [(Name, [LHsDoc GhcRn], SrcSpan)]
        -> HM.HashMap HCE.OccName HCE.DefinitionSite
      toHashMap =
        HM.fromListWith
          (\(HCE.DefinitionSite loc newDoc) (HCE.DefinitionSite _ oldDoc) ->
             HCE.DefinitionSite loc (mappend newDoc oldDoc)) .
        map
          (\(name, docs, srcSpan) ->
             let location = nameLocation (Just srcSpan) name
                 htmlDoc =
                   if not (null docs)
                     then let hsDocStrings = [ s | L _ (WithHsDocIdentifiers s _) <- docs ]
                              doc         = hsDocsToDocH unitState flags globalRdrEnv hsDocStrings
                          in  Just (docHToHtml doc)
                     else Nothing
              in (HCE.OccName $ toText name, HCE.DefinitionSite location htmlDoc))


  in ( HCE.DefinitionSiteMap
          { HCE.values    = toHashMap valuesWithDocumentation
          , HCE.types     = toHashMap (typesWithDocumentation ++ dataFamTyConsWithoutDocs)
          , HCE.instances = instancesWithDocumentation
          }
     , map (\(n, _, _) -> n) allNamesWithDocumentation
     )


occNameToHtml ::
     DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> (ModuleName, OccName)
  -> H.Html
occNameToHtml flags packageId compId (modName, occName) =
  let location =
        H.textValue . toStrict . encodeToLazyText . Aeson.toJSON $
        occNameLocationInfo flags packageId compId (modName, occName)
   in (H.span H.! H.dataAttribute "location" location) H.! A.class_ "link" $
      H.toHtml (toText occName)

nameToHtml ::
  UnitState
  -> DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> HCE.SourceCodeTransformation
  -> HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
  -> HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
  -> Name
  -> H.Html
nameToHtml unitState flags packageId compId transformation files defSiteMap name =
  let location =
        H.textValue . toStrict . encodeToLazyText . Aeson.toJSON $
        nameLocationInfo
          unitState
          flags
          packageId
          compId
          transformation
          files
          defSiteMap
          Nothing
          Nothing
          name
   in H.span H.! H.dataAttribute "location" location H.! A.class_ "link" $
      H.toHtml (nameToText name)

docWithNamesToHtml ::
  UnitState
  -> DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> HCE.SourceCodeTransformation
  -> HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
  -> HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
  -> DocH (ModuleName, OccName) Name
  -> HCE.HTML
docWithNamesToHtml unitState flags packageId compId transformation fileMap defSiteMap =
  HCE.docToHtml
    (occNameToHtml flags packageId compId)
    (nameToHtml unitState flags packageId compId transformation fileMap defSiteMap)

createDeclarations ::
     DynFlags
  -> HsGroup GhcRn
  -> TypeEnv
  -> S.Set Name
  -> HCE.SourceCodeTransformation
  -> [HCE.Declaration]
createDeclarations flags hsGroup typeEnv exportedSet transformation =
  let lineNumber :: SrcSpan -> Int
      lineNumber srcSpan =
        case srcSpanToLineAndColNumbers transformation srcSpan of
          Just (_file,(lineNum, _), (_, _)) -> lineNum
          Nothing -> 1
      nameType :: Name -> Maybe HCE.Type
      nameType n =
        case lookupIdInTypeEnv typeEnv n of
          Just i -> Just . mkType . varType $ i
          Nothing -> Nothing
      valToDeclarations :: LHsBindLR GhcRn GhcRn -> [HCE.Declaration]
      valToDeclarations (L locAnn bind) =
        let
          names :: [Name]
          names = collectHsBindBinders CollNoDictBinders bind
          loc   :: SrcSpan
          loc   = locA locAnn
        in
          map
            (\name ->
               HCE.Declaration
                 HCE.ValD
                 (toText name)
                 (nameType name)
                 (S.member name exportedSet)
                 (lineNumber loc))
            names
      vals = concatMap valToDeclarations $ hsGroupVals hsGroup
      -- | Data, newtype, type, type family, data family or class declaration
      --------------------------------------------------------------------------------
      tyClToDeclaration :: LTyClDecl GhcRn -> HCE.Declaration
      tyClToDeclaration (L locA' tyClDecl) =
        HCE.Declaration
          HCE.TyClD
          (T.append (tyClDeclPrefix tyClDecl) (toText $ tcdName tyClDecl))
          (nameType $ tcdName tyClDecl)
          (S.member (unLoc $ tyClDeclLName tyClDecl) exportedSet)
          (lineNumber (locA locA'))
      tyclds =
        map tyClToDeclaration
        . filter (isGoodSrcSpan . locA . getLocA)
        . concatMap group_tyclds . hs_tyclds
        $ hsGroup
      -- | Instances
      --------------------------------------------------------------------------------
      instToDeclaration :: LInstDecl GhcRn -> HCE.Declaration
      instToDeclaration (L locA' inst) =
        HCE.Declaration
          HCE.InstD
          (instanceDeclToText flags inst)
          Nothing
          True
          (lineNumber (locA locA'))
      insts =
        map instToDeclaration
        . filter (isGoodSrcSpan . locA . getLoc)
        . hsGroupInstDecls
        $ hsGroup
      -- | Foreign functions
      --------------------------------------------------------------------------------
      foreignFunToDeclaration ::
           LForeignDecl GhcRn -> HCE.Declaration
      foreignFunToDeclaration (L locA' fd) =
        let name = unLoc $ fd_name fd
        in HCE.Declaration
            HCE.ForD
            (toText name)
            (nameType name)
            True
            (lineNumber (locA locA'))
      fords = map foreignFunToDeclaration $ hs_fords hsGroup
      --------------------------------------------------------------------------------
   in L.sortOn HCE.lineNumber $ vals ++ tyclds ++ insts ++ fords

foldAST :: UnitState -> Environment -> TypecheckedModule -> SourceInfo
foldAST unitState environment typecheckedModule =
  let (Just renamed@(_hsGroupRn, importDecls, mbExported, _mbTopDoc, _mbModuleName)) =
        renamedSource typecheckedModule
      emptyASTState =
        ASTState IVM.empty IM.empty M.empty emptyTidyEnv Nothing environment []
      ASTState {..} =
        execState
          (foldTypecheckedSource $ tm_typechecked_source typecheckedModule)
          emptyASTState
      (idInfoMap, idOccMap) =
        L.foldl'
          (addIdentifierToMaps environment astStateIdSrcSpanMap)
          (HM.empty, astStateIdOccMap)
          (namesFromRenamedSource renamed)
      flags = envDynFlags environment
      packageId = envPackageId environment
      compId = envComponentId environment
      importedModules =
        map
          ((\(L ann modName) ->
              ( modName
              , locA ann
              , moduleLocationInfo
                  unitState
                  flags
                  (envModuleNameMap environment)
                  packageId
                  compId
                  modName)) .
          ideclName . unLoc) .
        filter (not . (ideclImplicit . ideclExt . unLoc)) $
        importDecls
      exportedModules =
        case mbExported of
          Just lieNames ->
            mapMaybe
              (\(L ann ie, _) ->
                case ie of
                  IEModuleContents _ (L _ modName) ->
                    Just
                      ( modName
                      , locA ann
                      , moduleLocationInfo
                          unitState
                          flags
                          (envModuleNameMap environment)
                          packageId
                          compId
                          modName)
                  _ -> Nothing)
              lieNames
          Nothing -> []
      addImportedAndExportedModulesToIdOccMap ::
           HCE.IdentifierOccurrenceMap -> HCE.IdentifierOccurrenceMap
      addImportedAndExportedModulesToIdOccMap =
        IM.map (L.sortOn fst) .
        addModules
          (envTransformation environment)
          (importedModules ++ exportedModules)
   in SourceInfo
        { sourceInfoExprMap = astStateExprInfoMap
        , sourceInfoIdMap = idInfoMap
        , sourceInfoIdOccMap = addImportedAndExportedModulesToIdOccMap idOccMap
        , sourceInfoTypeErrors = astStateTypeErrors
        }

-- | Updates 'IdentifierOccurrenceMap' and 'IdentifierInfoMap' using information
-- from typechecked source and renamed source
addIdentifierToMaps ::
     Environment
  -> M.Map RealSrcSpan (Id, Maybe (Type, [Type]))
  -> (HCE.IdentifierInfoMap, HCE.IdentifierOccurrenceMap)
  -> NameOccurrence
  -> (HCE.IdentifierInfoMap, HCE.IdentifierOccurrenceMap)
addIdentifierToMaps environment idSrcSpanMap idMaps@(idInfoMap, idOccMap) nameOcc
  | isGoodSrcSpan (getLoc $ locatedName nameOcc) &&
      isOneLineSpan (getLoc $ locatedName nameOcc)
  , Just (_, (lineNumber, startCol), (_, endCol)) <-
     srcSpanToLineAndColNumbers (envTransformation environment) .
     getLoc . locatedName $
     nameOcc =
    case nameOcc of
      TyLitOccurrence {kind = kind} ->
        addNameToMaps
          environment
          idMaps
          (Just kind)
          Nothing
          (description nameOcc)
          lineNumber
          startCol
          endCol
      NameOccurrence {isBinder = isBinder} ->
        case lookupIdByNameOccurrence environment idSrcSpanMap nameOcc of
          Just (identifier, mbTypes) ->
            let name =
                  fromMaybe
                    (varName identifier)
                    (unLoc $ locatedName nameOcc)
                identifierType = varType identifier
                identifierTypeExpanded = expandTypeSynonyms identifierType
                tyConsAndTyVars =
                  map
                    (, Nothing)
                    (tyConsOfType identifierType ++
                     tyVarsOfType identifierType ++
                     tyConsOfType identifierTypeExpanded ++
                     tyVarsOfType identifierTypeExpanded ++
                     maybe [] (tyConsOfType . fst) mbTypes ++
                     maybe [] (tyVarsOfType . fst) mbTypes)
                idInfoMap' =
                  updateIdMap
                    environment
                    ((identifier, unLoc $ locatedName nameOcc) : tyConsAndTyVars)
                    idInfoMap
                idOcc =
                  mkIdentifierOccurrence
                    environment
                    identifier
                    name
                    mbTypes
                    isBinder
                    (description nameOcc)
                idOccMap' =
                  IM.insertWith
                    removeOverlappingInterval
                    lineNumber
                    [((startCol, endCol), idOcc)]
                    idOccMap
             in (idInfoMap', idOccMap')
          Nothing -- type variable or an internal identifier in a pattern synonym
           ->
            case unLoc $ locatedName nameOcc of
              Just name ->
                addNameToMaps
                  environment
                  idMaps
                  Nothing
                  (Just name)
                  (description nameOcc)
                  lineNumber
                  startCol
                  endCol
              Nothing -> idMaps
addIdentifierToMaps _ _ idMaps _ = idMaps

addNameToMaps ::
     Environment
  -> (HCE.IdentifierInfoMap, HCE.IdentifierOccurrenceMap)
  -> Maybe Type
  -> Maybe Name
  -> T.Text
  -> Int
  -> Int
  -> Int
  -> (HCE.IdentifierInfoMap, HCE.IdentifierOccurrenceMap)
addNameToMaps environment (idInfoMap, idOccMap) mbKind mbName descr lineNumber colStart colEnd =
  let flags = envDynFlags environment
      idInfoMap' =
        maybe
          idInfoMap
          (\kind ->
             updateIdMap
               environment
               (map (, Nothing) $ tyConsOfType kind ++ tyVarsOfType kind)
               idInfoMap)
          mbKind
      idOcc =
        HCE.IdentifierOccurrence
          { internalId = fmap (HCE.InternalId . nameKey) mbName
          , internalIdFromRenamedSource =
              HCE.InternalId . T.pack . show . getKey . nameUnique <$> mbName
          , isBinder = False
          , instanceResolution = Nothing
          , idOccType = mkType <$> mbKind
          , typeArguments = Nothing
          , description = descr
          , sort =
              maybe
                HCE.TypeId
                (\name ->
                   case occNameNameSpace . nameOccName $ name of
                     HCE.VarName -> HCE.ValueId
                     HCE.DataName -> HCE.ValueId
                     _ -> HCE.TypeId)
                mbName
          }
      idOccMap' =
        IM.insertWith
          removeOverlappingInterval
          lineNumber
          [((colStart, colEnd), idOcc)]
          idOccMap
   in (idInfoMap', idOccMap')

lookupIdByNameOccurrence ::
     Environment
  -> M.Map RealSrcSpan (Id, Maybe (Type, [Type]))
  -> NameOccurrence
  -> Maybe (Id, Maybe (Type, [Type]))
lookupIdByNameOccurrence environment idSrcSpanMap (NameOccurrence (L span mbName) _ _) =
  case lookupBySrcSpan span of
    Just hit -> Just hit
    Nothing  ->
      case mbName of
        Just name ->
          case lookupBySrcSpan (nameSrcSpan name) of
            Just hit -> Just hit             -- LHS of a Match 等
            Nothing  ->
              -- 不在 typechecked 源里的名字，退回 TypeEnv
              case lookupIdInTypeEnv (envTypeEnv environment) name of
                Just t  -> Just (t, Nothing)
                Nothing -> Nothing
        Nothing -> Nothing
  where
    lookupBySrcSpan :: SrcSpan -> Maybe (Id, Maybe (Type, [Type]))
    lookupBySrcSpan s =
      case s of
        RealSrcSpan real _ -> M.lookup real idSrcSpanMap
        _                  -> Nothing
lookupIdByNameOccurrence _ _ TyLitOccurrence{} = Nothing

updateIdMap ::
     Environment
  -> [(Id, Maybe Name)]
  -> HCE.IdentifierInfoMap
  -> HCE.IdentifierInfoMap
updateIdMap environment ids identifiersMap =
  let flags = envDynFlags environment
      update ::
           HCE.IdentifierInfoMap -> (Id, Maybe Name) -> HCE.IdentifierInfoMap
      update idMap (identifier, mbName) =
        let info = mkIdentifierInfo environment identifier mbName
         in HM.insertWith
              (flip const)
              (HCE.InternalId $ identifierKey flags identifier)
              info
              idMap
   in L.foldl' update identifiersMap ids

addModules ::
     HCE.SourceCodeTransformation
  -> [(ModuleName, SrcSpan, HCE.LocationInfo)]
  -> HCE.IdentifierOccurrenceMap
  -> HCE.IdentifierOccurrenceMap
addModules transformation modules idMap =
  let update ::
           IM.IntMap [((Int, Int), HCE.IdentifierOccurrence)]
        -> (a, SrcSpan, HCE.LocationInfo)
        -> IM.IntMap [((Int, Int), HCE.IdentifierOccurrence)]
      update idOccMap (_modInfo, span, locInfo)
        | Just (_file,(lineNumber, colStart), (_, colEnd)) <-
           srcSpanToLineAndColNumbers transformation span =
          let idOcc =
                HCE.IdentifierOccurrence
                  { internalId = Nothing
                  , internalIdFromRenamedSource = Nothing
                  , isBinder = False
                  , instanceResolution = Nothing
                  , idOccType = Nothing
                  , typeArguments = Nothing
                  , description = "ImportDecl"
                  , sort = HCE.ModuleId locInfo
                  }
           in IM.insertWith
                removeOverlappingInterval
                lineNumber
                [((colStart, colEnd), idOcc)]
                idOccMap
      update idOccMap _ = idOccMap
   in L.foldl' update idMap modules
