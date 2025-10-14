{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedRecordDot #-}

module HaskellCodeExplorer.GhcUtils
  ( -- * Pretty-printing
    toText
  , instanceToText
  , instanceDeclToText
  , nameToText
  , tyClDeclPrefix
  , demangleOccName
  , stringBufferToByteString
  , nameSort
  , occNameNameSpace
  , identifierKey
  , nameKey
  , mbIdDetails
    -- * Syntax manipulation
  , hsGroupVals
  , hsPatSynDetails
  , ieLocNames
  , ghcDL  
    -- * Lookups
  , lookupIdInTypeEnv
  , lookupNameModuleAndPackage
    -- * Location info
  , isHsBoot
  , moduleLocationInfo
  , nameLocationInfo
  , occNameLocationInfo
  , nameDocumentation
  , srcSpanToLineAndColNumbers
    -- * Type-related functions
  , tyThingToId
  , tidyIdentifierType
  , patSynId
  , applyWrapper
  , wrapperTypes
  , tyVarsOfType
  , tyConsOfType
  , updateOccNames
  , mkType
    -- * Documentation processing
  , collectDocs
  , ungroup
  , mkDecls
  , getMainDeclBinder
  , classDeclDocs
  , sigNameNoLoc
  , clsInstDeclSrcSpan
  , hsDocsToDocH
  , subordinateNamesWithDocs
  , toHsDocStrings
  ) where
import           Documentation.Haddock.Parser (overIdentifier, parseParas)
import           Documentation.Haddock.Types (DocH(..), Header(..), _doc)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BSI
import           Data.Char (isAlpha, isAlphaNum, isAscii, ord)
import           Data.Either (either)
import           Data.Generics (Data)
import           Data.Generics.SYB (everything, everywhere, mkQ, mkT)
import qualified Data.Generics.Uniplate.Data()
import           Data.Hashable (Hashable,hash)
import qualified Data.HashMap.Strict as HM
import qualified Data.List as L
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe, isJust, mapMaybe, maybeToList)
import qualified Data.Text as T
import           GHC ( ClsInstDecl(..), ConDecl(..), DataDefnCons(..), DataFamInstDecl(..), DocDecl(..)
                     , DynFlags, FixitySig(..), HsBindLR(..), HsConDetails(..), HsDataDefn(..)
                     , HsDecl(..), HsDocString, HsGroup(..), HsPatSynDetails, HsValBindsLR(..)
                     , IE(..), Id, InstDecl(..), LHsDecl, LIEWrappedName, Located, LSig
                     , ModuleName, Name, NHsValBindsLR(..), NewOrData(..)
                     , RealSrcSpan(..), Sig(..), SrcSpan(..), TyClDecl(..)
                     , TyThing(..), collectHsBindBinders, getConNames, getLoc, hsGroupInstDecls
                     , hsSigWcType, hst_body, idType, ieLWrappedName, isDataFamilyDecl
                     , isExternalName, isGoodSrcSpan, isLocalId, moduleNameString
                     , nameSrcSpan, recordPatSynPatVar, srcSpanEndCol, srcSpanEndLine
                     , srcSpanFile, srcSpanStartCol, srcSpanStartLine, tfid_eqn
                     , tcdName, tyClGroupTyClDecls, tyFamInstDeclName, unpackHDSC)
import           GHC.Builtin.Types (unitTy)
import           GHC.Core.ConLike (ConLike(..))
import           GHC.Core.Coercion (coercionType)
import           GHC.Core.DataCon (dataConWorkId, flSelector)
import           GHC.Core.InstEnv (ClsInst(..))
import           GHC.Core.PatSyn (PatSyn, patSynMatcher, patSynSig)
import           GHC.Core.TyCo.Ppr (pprType)
import           GHC.Core.TyCo.Rep (scaledThing, Type(..))
import           GHC.Core.TyCon (tyConName, tyConKind)
import           GHC.Core.Type (coreView, expandTypeSynonyms, mkForAllTy, mkInvisForAllTys
                               , mkScaledFunTys, mkVisFunTyMany, piResultTy, splitFunTy_maybe
                               , tidyOpenType)
import           GHC.CoreToIface (toIfaceType)
import           GHC.Data.Bag (bagToList)
import           GHC.Data.FastString (fsLit, mkFastString, unpackFS)
import           GHC.Data.Pair (pSnd)
import           GHC.Data.StringBuffer (StringBuffer(..), stringToStringBuffer)
import           GHC.Driver.Config.Diagnostic (initDiagOpts)
import           GHC.Driver.Config.Parser (initParserOpts)
import           GHC.Driver.Session (DynFlags(..), extensionFlags)
import           GHC.Hs (collectPatBinders, ConDeclField(..), feqn_pats, feqn_rhs, feqn_tycon
                        , FieldOcc(..), ForeignExport, ForeignImport, GhcPass, GhcPs, GhcRn, IdP
                        , LIdP, locA, noExtField, XRec, unXRec)
import           GHC.Hs.Decls (HsDataDefn(..), ForeignDecl(..), ForeignImport(..), ForeignExport(..))
import           GHC.Hs.Doc (LHsDoc, renderHsDocString, WithHsDocIdentifiers(..))
import           GHC.Hs.Utils (CollectFlag(..))
import           GHC.Parser (parseIdentifier)
import           GHC.Parser.Lexer (initParserState, mkParserOpts, ParseResult(POk), PState
                                  , unP)
import           GHC.Parser.Annotation (AnnListItem, EpAnn, getLocA, SrcSpanAnnA, noLocA)
import           GHC.Tc.Types.Evidence (HsWrapper(..))
import           GHC.Tc.Utils.TcType (evVarPred)
import           GHC.Types.Id (mkVanillaGlobal)
import           GHC.Types.Id.Info (IdDetails(..))
import           GHC.Types.Name (isDataConNameSpace, isDerivedOccName, isInternalName
                                , isSystemName, isTvNameSpace, isTyConName, isValNameSpace
                                , isWiredInName, mkInternalName, mkOccName, nameModule_maybe
                                , nameOccName, nameUnique, OccName, occNameFS, occNameSpace
                                , occNameString, wiredInNameTyThing_maybe)
import           GHC.Types.Name.Reader ( GlobalRdrEnv, RdrName(..), gre_name, LookupGRE(..)
                                       , lookupGRE, mkRdrUnqual, rdrNameOcc, WhichGREs(..))
import           GHC.Types.Name.Occurrence (mkVarOcc, mkDataOcc, mkTcOcc)
import           GHC.Types.PkgQual (PkgQual(..))
import           GHC.Types.SrcLoc ( GenLocated(..), isGoodSrcSpan, mkRealSrcLoc, noLoc, RealSrcLoc
                                  , realSrcSpanStart , SrcSpan(..), UnhelpfulSpanReason(..)
                                  , unLoc)
import           GHC.Types.TypeEnv (TypeEnv, lookupTypeEnv)
import           GHC.Types.Unique (getKey)
import           GHC.Types.Unique.FM (lookupUFM)
import           GHC.Types.Unique.Set (emptyUniqSet, nonDetEltsUniqSet, unionUniqSets)
import           GHC.Types.Var ( ForAllTyFlag(..), idDetails, isId, mkTyVar, mkTyVarBinder
                               , setVarType, Specificity(..), varName, varType, varUnique)
import           GHC.Types.Var.Env (TidyEnv)
import           GHC.Types.Var.Set (VarSet, emptyVarSet, unionVarSet, unitVarSet)
import qualified GHC.Unit.Module as Mod
import           GHC.Unit.Module (Module, moduleUnitId)
import           GHC.Unit.Env (ue_units, UnitEnv)
import           GHC.Unit.Info (unitPackageName, unitPackageNameString, unitPackageVersion)
import           GHC.Unit.State (LookupResult(..), lookupModuleWithSuggestions, lookupUnit
                                , lookupUnitId, UnitInfo(..), unitInfoMap, UnitState(..))
import           GHC.Unit.Types (Unit)
import           GHC.Utils.Outputable (Outputable, ppr, showPprUnsafe, showSDocUnsafe)
import qualified HaskellCodeExplorer.Types as HCE
import           Prelude hiding (span)
import           System.FilePath (normalise)

--------------------------------------------------------------------------------
-- Pretty-printing
--------------------------------------------------------------------------------

toText :: (Outputable a) => a -> T.Text
toText x = T.pack $ showSDocUnsafe (ppr x)

instanceToText :: DynFlags -> ClsInst -> T.Text
instanceToText flags ClsInst {..} =
  T.append "instance " $ T.pack . showSDocUnsafe $ pprType (idType is_dfun)

instanceDeclToText :: DynFlags -> InstDecl GhcRn -> T.Text
instanceDeclToText flags decl =
  case decl of
    XInstDecl _ -> ""
    ClsInstD _ (XClsInstDecl _) -> ""
    ClsInstD _ ClsInstDecl {..} ->
      T.append "instance " (toText cid_poly_ty)

    DataFamInstD _ di ->
      let args =
            T.intercalate " " . map toText .  feqn_pats  . dfid_eqn $ di
       in T.concat
            ["data instance ", toText (unLoc $ feqn_tycon . dfid_eqn $ di), " ", args]
    TyFamInstD _ ti ->
      let args =
            T.intercalate " " .
            map toText . feqn_pats . tfid_eqn $
            ti
       in T.concat
            ["type instance ", toText $ tyFamInstDeclName ti, " ", args]

nameToText :: Name -> T.Text
nameToText = T.pack . unpackFS . occNameFS . nameOccName

tyClDeclPrefix :: TyClDecl a -> T.Text
tyClDeclPrefix tyClDecl =
   let  isNewTy :: TyClDecl pass -> Bool
        isNewTy DataDecl{ tcdDataDefn = HsDataDefn{ dd_cons = NewTypeCon{} } } = True
        isNewTy _ = False
   in case tyClDecl of
        FamDecl {}
          | isDataFamilyDecl tyClDecl -> "data family "
          | otherwise -> "type family "
        SynDecl {} -> "type "
        DataDecl {}
          | isNewTy tyClDecl -> "newtype "
          | otherwise -> "data "
        ClassDecl {} -> "class "
        XTyClDecl _ -> ""

demangleOccName :: Name -> T.Text
demangleOccName name
  | isDerivedOccName (nameOccName name) =
    let removePrefix :: T.Text -> T.Text
        removePrefix occName
          | T.isPrefixOf "$sel:" occName =
            fst $ T.breakOn ":" (T.drop 5 occName)
          | T.isPrefixOf "$W" occName = T.drop 2 occName
          | T.isPrefixOf "$w" occName = T.drop 2 occName
          | T.isPrefixOf "$m" occName = T.drop 2 occName
          | T.isPrefixOf "$b" occName = T.drop 2 occName
          | T.isPrefixOf "$dm" occName = T.drop 3 occName
          | T.isPrefixOf "$c" occName = T.drop 2 occName
          | T.isPrefixOf "$d" occName = T.drop 2 occName
          | T.isPrefixOf "$i" occName = T.drop 2 occName
          | T.isPrefixOf "$s" occName = T.drop 2 occName
          | T.isPrefixOf "$f" occName = T.drop 2 occName
          | T.isPrefixOf "$r" occName = T.drop 2 occName
          | T.isPrefixOf "C:" occName = T.drop 2 occName
          | T.isPrefixOf "N:" occName = T.drop 2 occName
          | T.isPrefixOf "D:" occName = T.drop 2 occName
          | T.isPrefixOf "$co" occName = T.drop 3 occName
          | otherwise = occName
     in removePrefix $ nameToText name
  | otherwise = nameToText name

stringBufferToByteString :: StringBuffer -> BS.ByteString
stringBufferToByteString (StringBuffer buf len cur) =
  BSI.fromForeignPtr buf cur len

nameSort :: Name -> HCE.NameSort
nameSort n =
  if isExternalName n
    then HCE.External
    else HCE.Internal

occNameNameSpace :: OccName -> HCE.NameSpace
occNameNameSpace n
  | isDataConNameSpace (occNameSpace n) = HCE.DataName
  | isTvNameSpace (occNameSpace n) = HCE.TvName
  | isValNameSpace (occNameSpace n) = HCE.VarName
  | otherwise = HCE.TcClsName

-- Two 'Id''s may have different types even though they have the same 'Unique'.
identifierKey :: DynFlags -> Id -> T.Text
identifierKey flags id
  | isLocalId id =
    T.concat
      [ T.pack . show . getKey . varUnique $ id
      , "_"
      , T.pack . show . hash . showSDocUnsafe . ppr . varType $ id
      ]
identifierKey _ id = T.pack . show . getKey . varUnique $ id

nameKey :: Name -> T.Text
nameKey = T.pack . show . getKey . nameUnique

mbIdDetails :: Id -> Maybe HCE.IdDetails
mbIdDetails v
  | isId v =
    case idDetails v of
      VanillaId -> Just HCE.VanillaId
      RecSelId {sel_naughty = False} -> Just HCE.RecSelId
      RecSelId {sel_naughty = True} -> Just HCE.RecSelIdNaughty
      DataConWorkId _ -> Just HCE.DataConWorkId
      DataConWrapId _ -> Just HCE.DataConWrapId
      ClassOpId _ _ -> Just HCE.ClassOpId
      RepPolyId _ -> Just HCE.RepPolyId
      PrimOpId _ _ -> Just HCE.PrimOpId
      FCallId _ -> Just HCE.FCallId
      TickBoxOpId _ -> Just HCE.TickBoxOpId
      DFunId _ -> Just HCE.DFunId
      CoVarId -> Just HCE.CoVarId
      JoinId _ _ -> Just HCE.JoinId
      WorkerLikeId _ -> Just HCE.WorkerLikeId
mbIdDetails _ = Nothing

--------------------------------------------------------------------------------
--  Syntax transformation
--------------------------------------------------------------------------------

hsGroupVals :: HsGroup GhcRn -> [GenLocated (EpAnn AnnListItem) (HsBindLR GhcRn GhcRn)]
hsGroupVals hsGroup =
  filter (isGoodSrcSpan . locA . getLoc) $
    case hs_valds hsGroup of
      XValBindsLR (NValBinds binds _) -> concatMap (bagToList . snd) binds
      _ -> []

hsPatSynDetails :: HsPatSynDetails a -> [LIdP a]
hsPatSynDetails patDetails =
  case patDetails of
    InfixCon name1 name2 -> [name1, name2]
    PrefixCon _ fields -> fields
    RecCon fields -> map recordPatSynPatVar fields

unwrapName :: LIEWrappedName (GhcPass p) -> LIdP (GhcPass p)
unwrapName = ieLWrappedName

ieLocNames :: IE (GhcPass p) -> [LIdP (GhcPass p)]
ieLocNames (XIE _) = []
ieLocNames (IEVar _ n _) = [unwrapName n]
ieLocNames (IEThingAbs _ n _) = [unwrapName n]
ieLocNames (IEThingAll _ n _) = [unwrapName n]
ieLocNames (IEThingWith _ n _ ns _) = unwrapName n : (map unwrapName ns)
ieLocNames IEModuleContents {} = []
ieLocNames IEGroup {} = []
ieLocNames IEDoc {} = []
ieLocNames IEDocNamed {} = []

--------------------------------------------------------------------------------
-- Lookups
--------------------------------------------------------------------------------

lookupIdInTypeEnv :: TypeEnv -> Name -> Maybe Id
lookupIdInTypeEnv typeEnv name = do
  let mbTyThing
        | isInternalName name = Nothing
        | isSystemName name = Nothing
        | isWiredInName name = wiredInNameTyThing_maybe name
        | isExternalName name = lookupTypeEnv typeEnv name
        | otherwise = Nothing
  case mbTyThing of
    Just tyThing -> tyThingToId tyThing
    _ -> Nothing

lookupNameModuleAndPackage ::
     UnitState
  -> HCE.PackageId
  -> Name
  -> Either T.Text (HCE.HaskellModuleName, HCE.PackageId)
lookupNameModuleAndPackage unitState currentPackageId name =
  case nameModule_maybe name of
    Just m ->
      case lookupUnit unitState (Mod.moduleUnit m) of
        Just packageConfig ->
          let packageId =
                if (T.pack $ unitPackageNameString packageConfig) == currentPackageId.name
                  then currentPackageId
                  else HCE.PackageId
                         (T.pack $ (unitPackageNameString packageConfig))
                         packageConfig.unitPackageVersion
           in Right
                ( HCE.HaskellModuleName . T.pack . moduleNameString $ Mod.moduleName m
                , packageId)
        Nothing ->
          Right
            ( HCE.HaskellModuleName . T.pack . moduleNameString $ Mod.moduleName m
            , currentPackageId)
    Nothing ->
      Left $ T.concat ["nameModule_maybe ", nameToText name, " is Nothing"]

--------------------------------------------------------------------------------
-- Location info
--------------------------------------------------------------------------------

isHsBoot :: HCE.HaskellModulePath -> Bool
isHsBoot = T.isSuffixOf "-boot" . HCE.getHaskellModulePath

moduleLocationInfo ::
     UnitState
  -> DynFlags
  -> HM.HashMap HCE.HaskellModuleName (HM.HashMap HCE.ComponentId HCE.HaskellModulePath)
  -> HCE.PackageId
  -> HCE.ComponentId
  -> ModuleName
  -> HCE.LocationInfo
moduleLocationInfo unitState flags moduleNameMap currentPackageId compId moduleName =
  let moduleNameText = T.pack . moduleNameString $ moduleName
      currentPackageLocation =
        HCE.ApproximateLocation
          currentPackageId
          (HCE.HaskellModuleName . T.pack . moduleNameString $ moduleName)
          HCE.Mod
          moduleNameText
          Nothing
          compId
   in case HM.lookup (HCE.HaskellModuleName moduleNameText) moduleNameMap of
        Just modulePathMap
          | Just modulePath <- HM.lookup compId modulePathMap ->
            HCE.ExactLocation
              currentPackageId
              modulePath
              (HCE.HaskellModuleName moduleNameText)
              1
              1
              1
              1
        _ ->
          case lookupModuleWithSuggestions unitState moduleName NoPkgQual of
            LookupFound m _ ->
              let unitId = Mod.moduleUnit m in
              case lookupUnit unitState unitId of
                Just packInfo ->
                  let packageId =
                        HCE.PackageId
                          (T.pack $ unitPackageNameString packInfo)
                          (unitPackageVersion packInfo)
                   in HCE.ApproximateLocation
                        packageId
                        (HCE.HaskellModuleName . T.pack . moduleNameString $
                         moduleName)
                        HCE.Mod
                        moduleNameText
                        Nothing
                        (if packageId == currentPackageId
                           then compId
                           else HCE.ComponentId "lib")
                Nothing -> currentPackageLocation
            _ -> currentPackageLocation

isDefinedInCurrentModule :: HCE.SourceCodeTransformation -> HCE.HaskellFilePath -> Bool
isDefinedInCurrentModule transformation file =
  let includedFiles = HM.keys $ HCE.fileIndex transformation
      modPath = HCE.getHaskellModulePath transformation.filePath
   in HCE.getHaskellFilePath file == modPath || (file `elem` includedFiles)

nameLocationInfo ::
  UnitState
  -> DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> HCE.SourceCodeTransformation
  -> HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
  -> HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
  -> Maybe T.Text -- ^ Instance head (when name is a dictionary function)
  -> Maybe SrcSpan -- ^ Only for wired-in names
  -> Name
  -> HCE.LocationInfo
nameLocationInfo unitState flags currentPackageId compId transformation fileMap defSiteMap mbInstanceHead mbSrcSpan name
  | Just srcSpan <- realSrcSpan name mbSrcSpan =
    let filePath =
          HCE.HaskellFilePath . T.pack . normalise . unpackFS . srcSpanFile $
          srcSpan
        approximateLocation = mkApproximateLocation unitState flags currentPackageId compId mbInstanceHead name
     in if isDefinedInCurrentModule transformation filePath
          then let eitherStart =
                     HCE.fromOriginalLineNumber
                       transformation
                       (filePath, srcSpanStartLine srcSpan)
                   eitherEnd =
                     HCE.fromOriginalLineNumber
                       transformation
                       (filePath, srcSpanEndLine srcSpan)
                in case (,) eitherStart eitherEnd of
                     (Right startLine,Right endLine) ->
                         let  modulePath = (transformation :: HCE.SourceCodeTransformation).filePath
                              moduleName =
                                  either
                                    (const $ HCE.HaskellModuleName "")
                                    fst
                                    (lookupNameModuleAndPackage unitState currentPackageId name)
                         in HCE.ExactLocation
                              { packageId = currentPackageId
                              , modulePath = modulePath
                              , moduleName = moduleName
                              , startLine = startLine
                              , endLine = endLine
                              , startColumn = srcSpanStartCol srcSpan
                              , endColumn = srcSpanEndCol srcSpan
                              }
                     _ -> approximateLocation
          else case HM.lookup filePath fileMap of
                 Just haskellModulePath ->
                   case HM.lookup haskellModulePath defSiteMap of
                     Just defSites ->
                       let key = fromMaybe (nameToText name) mbInstanceHead
                        in lookupEntityLocation
                             defSites
                             (mkLocatableEntity name mbInstanceHead)
                             key
                     Nothing -> approximateLocation
                 Nothing -> approximateLocation
  where
    realSrcSpan :: Name -> Maybe SrcSpan -> Maybe RealSrcSpan
    realSrcSpan n mbSpan =
      case nameSrcSpan n of
        RealSrcSpan span _ -> Just span
        _
          | isWiredInName n ->
            case mbSpan of
              Just span ->
                case span of
                  RealSrcSpan s _ -> Just s
                  _ -> Nothing
              _ -> Nothing
        _ -> Nothing
nameLocationInfo unitState flags currentPackageId compId _transformation _fileMap _defSiteMap mbInstanceHead _mbSrcSpan name =
  mkApproximateLocation unitState flags currentPackageId compId mbInstanceHead name

mkApproximateLocation ::
  UnitState
  -> DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> Maybe T.Text
  -> Name
  -> HCE.LocationInfo
mkApproximateLocation unitState flags currentPackageId compId mbInstanceHead name =
  let haddockAnchor =
        Just . T.pack . makeAnchorId . T.unpack . nameToText $ name
   in case lookupNameModuleAndPackage unitState currentPackageId name of
        Right (moduleName, packageId) ->
          HCE.ApproximateLocation
            { moduleName = moduleName
            , packageId = packageId
            , componentId =
                if packageId == currentPackageId
                  then compId
                  else HCE.ComponentId "lib"
            , entity = mkLocatableEntity name mbInstanceHead
            , haddockAnchorId = haddockAnchor
            , name = fromMaybe (nameToText name) mbInstanceHead
            }
        Left errorMessage -> HCE.UnknownLocation errorMessage

mkLocatableEntity :: Name -> Maybe a -> HCE.LocatableEntity
mkLocatableEntity name mbInstanceHead
  | isJust mbInstanceHead = HCE.Inst
  | otherwise =
    case occNameNameSpace . nameOccName $ name of
      HCE.VarName -> HCE.Val
      HCE.DataName -> HCE.Val
      _ -> HCE.Typ

occNameLocationInfo ::
     DynFlags
  -> HCE.PackageId
  -> HCE.ComponentId
  -> (ModuleName, OccName)
  -> HCE.LocationInfo
occNameLocationInfo flags packageId componentId (modName, occName) =
  HCE.ApproximateLocation
    { packageId = packageId
    , moduleName = HCE.HaskellModuleName $ toText modName
    , entity =
        case occNameNameSpace occName of
          HCE.VarName -> HCE.Val
          HCE.DataName -> HCE.Val
          _ -> HCE.Typ
    , name = toText occName
    , haddockAnchorId =
        Just . T.pack . makeAnchorId . T.unpack $ toText occName
    , componentId = componentId
    }

lookupEntityLocation ::
     HCE.DefinitionSiteMap -> HCE.LocatableEntity -> T.Text -> HCE.LocationInfo
lookupEntityLocation defSiteMap locatableEntity text =
  let errorMessage =
        T.concat
          [ "Cannot find location of "
          , T.pack . show $ locatableEntity
          , " "
          , text
          ]
      lookupLocation ::
           (Eq a, Hashable a)
        => (HCE.DefinitionSiteMap -> HM.HashMap a HCE.DefinitionSite)
        -> (T.Text -> a)
        -> HCE.LocationInfo
      lookupLocation selector toKey =
        maybe (HCE.UnknownLocation errorMessage) (\siteMap -> siteMap.location) $
        HM.lookup (toKey text) (selector defSiteMap)
   in case locatableEntity of
        HCE.Val -> lookupLocation (\siteMap -> siteMap.values) HCE.OccName
        HCE.Typ -> lookupLocation (\siteMap -> siteMap.types) HCE.OccName
        HCE.Inst -> lookupLocation (\siteMap -> siteMap.instances) (\t -> t)
        HCE.Mod -> HCE.UnknownLocation errorMessage

nameDocumentation ::
     HCE.SourceCodeTransformation
  -> HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
  -> HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
  -> HCE.DefinitionSiteMap
  -> Name
  -> Maybe T.Text
nameDocumentation transformation fileMap defSiteMap currentModuleDefSiteMap name
  | isExternalName name || isWiredInName name
  , Just file <- srcSpanToFilePath . nameSrcSpan $ name =
    if isDefinedInCurrentModule transformation file
      then lookupNameDocumentation name currentModuleDefSiteMap
      else case HM.lookup file fileMap of
             Just haskellModulePath ->
               case HM.lookup haskellModulePath defSiteMap of
                 Just defSites -> lookupNameDocumentation name defSites
                 Nothing -> Nothing
             Nothing -> Nothing
nameDocumentation _ _ _ _ _ = Nothing

lookupNameDocumentation :: Name -> HCE.DefinitionSiteMap -> Maybe T.Text
lookupNameDocumentation name defSiteMap =
  let key = HCE.OccName $ nameToText name
      lookupDoc ::
           (HCE.DefinitionSiteMap -> HM.HashMap HCE.OccName HCE.DefinitionSite)
        -> Maybe T.Text
      lookupDoc selector =
        maybe Nothing HCE.documentation $
        HM.lookup key (selector (defSiteMap :: HCE.DefinitionSiteMap))
   in case occNameNameSpace . nameOccName $ name of
        HCE.VarName -> lookupDoc (\siteMap -> siteMap.values)
        HCE.DataName -> lookupDoc (\siteMap -> siteMap.values)
        _ -> lookupDoc (\siteMap -> siteMap.types)

srcSpanToFilePath :: SrcSpan -> Maybe HCE.HaskellFilePath
srcSpanToFilePath (RealSrcSpan s _) =
  Just . HCE.HaskellFilePath . T.pack . normalise . unpackFS . srcSpanFile $ s
srcSpanToFilePath (UnhelpfulSpan _) = Nothing

srcSpanToLineAndColNumbers ::
     HCE.SourceCodeTransformation
  -> SrcSpan
  -> Maybe (HCE.HaskellFilePath, (Int, Int), (Int, Int))
srcSpanToLineAndColNumbers transformation (RealSrcSpan s _) =
  let filePath =
        HCE.HaskellFilePath . T.pack . normalise . unpackFS . srcSpanFile $ s
      eitherStart =
        HCE.fromOriginalLineNumber transformation (filePath, srcSpanStartLine s)
      eitherEnd =
        HCE.fromOriginalLineNumber transformation (filePath, srcSpanEndLine s)
   in case (,) eitherStart eitherEnd of
        (Right startLine, Right endLine) ->
          Just
            ( filePath
            , (startLine, srcSpanStartCol s)
            , (endLine, srcSpanEndCol s))
        _ -> Nothing
srcSpanToLineAndColNumbers _ _ = Nothing

--------------------------------------------------------------------------------
-- Type-related functions
--------------------------------------------------------------------------------

tyThingToId :: TyThing -> Maybe Id
tyThingToId tyThing =
  case tyThing of
    AnId id -> Just id
    ATyCon tc -> Just $ mkTyVar (tyConName tc) (tyConKind tc)
    AConLike con ->
      case con of
        RealDataCon dataCon -> Just $ dataConWorkId dataCon
        PatSynCon ps -> Just $ patSynId ps
    ACoAxiom _ -> Nothing

tidyIdentifierType :: TidyEnv -> Id -> (TidyEnv, Id)
tidyIdentifierType tidyEnv identifier =
  let (tidyEnv', typ') = tidyOpenType tidyEnv (varType identifier)
   in (tidyEnv', setVarType identifier typ')

mkFunTys :: [Type] -> Type -> Type
mkFunTys ts init = foldr mkVisFunTyMany init ts

patSynId :: PatSyn -> Id
patSynId patSyn =
  let (univTvs, reqTheta, exTvs, provTheta, argTys, resTy) = patSynSig patSyn
      reqTheta'
        | null reqTheta && not (null provTheta && null exTvs) = [unitTy]
        | otherwise = reqTheta
      --  required => provided => arg_1 -> ... -> arg_n -> res
      ubinders = map (mkTyVarBinder SpecifiedSpec) univTvs
      xbinders = map (mkTyVarBinder SpecifiedSpec) exTvs
      patSynTy =
        mkInvisForAllTys ubinders $
        mkFunTys reqTheta' $
        mkInvisForAllTys xbinders $
        mkFunTys provTheta $ mkScaledFunTys argTys resTy
   in
      let (matcherName, _, _) = patSynMatcher patSyn
      in mkVanillaGlobal matcherName patSynTy


applyWrapper :: HsWrapper -> Type -> Type
applyWrapper wp ty
  | Just ty' <- coreView ty = applyWrapper wp ty'
applyWrapper WpHole t = t
applyWrapper (WpCompose w1 w2) t = applyWrapper w1 . applyWrapper w2 $ t
applyWrapper (WpFun w1 w2 t1) t =
  let argTy   = applyWrapper w1 (scaledThing t1)
      resTy   = piResultTy t argTy
  in  mkScaledFunTys [t1] (applyWrapper w2 resTy)
applyWrapper (WpCast coercion) _t = coercionType coercion
applyWrapper (WpEvLam v) t = mkVisFunTyMany (evVarPred v) t
applyWrapper (WpEvApp _ev) t = case splitFunTy_maybe t of
  Just (_, _, _,res) -> res
  Nothing -> t
applyWrapper (WpTyLam v) t = mkInvisForAllTys [mkTyVarBinder SpecifiedSpec v] t
applyWrapper (WpTyApp t') t = piResultTy t t'
applyWrapper (WpLet _) t = t

wrapperTypes :: HsWrapper -> [Type]
wrapperTypes WpHole  = []
wrapperTypes (WpCompose w1 w2) = wrapperTypes w2 ++ wrapperTypes w1
wrapperTypes (WpFun w1 w2 _) = wrapperTypes w2 ++ wrapperTypes w1
wrapperTypes (WpCast _)  = []
wrapperTypes (WpEvLam _) = []
wrapperTypes (WpEvApp _) = []
wrapperTypes (WpTyLam _) = []
wrapperTypes (WpTyApp t) = [t]
wrapperTypes (WpLet _) = []

mkType :: Type -> HCE.Type
mkType typ =
  let typeExpanded = expandTypeSynonyms typ
      typeComponents = toTypeComponents typ
      typeComponentsExpanded = toTypeComponents typeExpanded
   in HCE.Type
        typeComponents
        (if typeComponents /= typeComponentsExpanded
           then Just typeComponentsExpanded
           else Nothing)

typeToText :: Type -> T.Text
typeToText = T.pack . showSDocUnsafe . ppr . toIfaceType

toTypeComponents :: Type -> [HCE.TypeComponent]
toTypeComponents typ =
  let signature =
        typeToText $
        updateOccNames (\_unique occName -> ";" ++ drop 2 occName ++ ";") typ
      -- Signature with OccNames and uniques
      signatureWithUniques =
        typeToText $
        updateOccNames
          (\unique occName -> ";," ++ occName ++ "," ++ unique ++ ";")
          typ
      -- Dirty but simple way to extract a list of TypeComponent from a type signature.
      -- Assumptions :
      -- 1. Character ';' cannot appear anywhere in a type signature
      -- 2. Character ',' cannot appear in an 'OccName'
      -- 3. length (T.splitOn ";" signature) == length (T.splitOn ";" signatureWithUniques)
      components =
        L.zip (T.splitOn ";" signature) (T.splitOn ";" signatureWithUniques)
   in mapMaybe
        (\(text1, text2) ->
           if T.isPrefixOf "," text2
             then case T.splitOn "," text2 of
                    ["", name, id] ->
                      Just HCE.TyCon {name = name, internalId = HCE.InternalId id}
                    _ -> Just $ HCE.Text text1
             else if T.null text1
                    then Nothing
                    else Just $ HCE.Text text1)
        components

-- | Replaces 'OccName' of each type variable and type constructor in a type.
updateOccNames :: (String -> String -> String) -> Type -> Type
updateOccNames update = everywhere (mkT updateType)
  where
    updateType :: Type -> Type
    updateType (TyVarTy var) = TyVarTy var {varName = updateName (varName var)}
    updateType (TyConApp con args) =
      TyConApp (con {tyConName = updateName (tyConName con)}) args
    updateType other = other
    updateName :: Name -> Name
    updateName oldName =
      let oldOccName = nameOccName oldName
          unique = T.unpack $ nameKey oldName
          newOccName =
            mkOccName
              (occNameSpace oldOccName)
              (update unique (occNameString oldOccName))
       in mkInternalName (nameUnique oldName) newOccName (nameSrcSpan oldName)

-- | This function doesn't look through type synonyms
tyConsOfType :: Type -> [Id]
tyConsOfType =
  nonDetEltsUniqSet . everything unionUniqSets (emptyVarSet `mkQ` tyCon)
  where
    tyCon :: Type -> VarSet
    tyCon (TyConApp tc _) = unitVarSet $ mkTyVar (tyConName tc) (tyConKind tc)
    tyCon _ = emptyUniqSet

tyVarsOfType :: (Data a) => a -> [Id]
tyVarsOfType = nonDetEltsUniqSet . everything unionVarSet (emptyVarSet `mkQ` tyVar)
  where
    tyVar :: Type -> VarSet
    tyVar (TyVarTy ty) = unitVarSet ty
    tyVar _ = emptyVarSet

--------------------------------------------------------------------------------
-- Documentation processing
-- Some functions are copied from haddock-api package
--------------------------------------------------------------------------------

collectDocs :: [LHsDecl GhcRn] -> [(LHsDecl GhcRn, [LHsDoc GhcRn])]
collectDocs = go Nothing []
  where
    go Nothing _ [] = []
    go (Just prev) docs [] = finished prev docs []
    go prev docs (L _ (DocD _ (DocCommentNext str)):ds)
      | Nothing <- prev = go Nothing (str : docs) ds
      | Just decl <- prev = finished decl docs (go Nothing [str] ds)
    go prev docs (L _ (DocD _ (DocCommentPrev str)):ds) = go prev (str : docs) ds
    go Nothing docs (d:ds) = go (Just d) docs ds
    go (Just prev) docs (d:ds) = finished prev docs (go (Just d) [] ds)
    finished decl docs rest = (decl, reverse docs) : rest

ungroup :: HsGroup GhcRn -> [LHsDecl GhcRn]
ungroup group_ =
  mkDecls (tyClGroupTyClDecls . hs_tyclds) (TyClD noExtField) group_ ++
  mkDecls hs_derivds (DerivD noExtField) group_ ++
  mkDecls hs_defds (DefD noExtField) group_ ++
  mkDecls hs_fords (ForD noExtField) group_ ++
  mkDecls hs_docs (DocD noExtField) group_ ++
  mkDecls hsGroupInstDecls (InstD noExtField) group_ ++
  mkDecls (typesigs . hs_valds) (SigD noExtField) group_ ++
  mkDecls (valbinds . hs_valds) (ValD noExtField) group_
  where
    typesigs (XValBindsLR (NValBinds _ sigs)) = filter isUserLSig sigs
    typesigs _ = []
    valbinds (XValBindsLR (NValBinds binds _)) = concatMap (bagToList . snd) binds
    valbinds _ = []

mkDecls :: (a -> [GenLocated (EpAnn AnnListItem) b]) -> (b -> HsDecl GhcRn) -> a -> [LHsDecl GhcRn]
mkDecls field con struct = [L loc (con decl) | L loc decl <- field struct]

srcSpanStartOrDummy :: SrcSpan -> RealSrcLoc
srcSpanStartOrDummy (RealSrcSpan realSpan _) = realSrcSpanStart realSpan
srcSpanStartOrDummy (UnhelpfulSpan _)        = mkRealSrcLoc (mkFastString "<no-file>") 0 0

sortByLocA :: [GenLocated SrcSpanAnnA a] -> [GenLocated SrcSpanAnnA a]
sortByLocA = L.sortOn (srcSpanStartOrDummy . locA . getLoc)

classDeclDocs :: TyClDecl GhcRn -> [(LHsDecl GhcRn, [LHsDoc GhcRn])]
classDeclDocs class_ = collectDocs . sortByLocA $ decls
  where
    decls = docs ++ defs ++ sigs ++ ats
    docs = mkDecls tcdDocs (DocD noExtField) class_
    defs = mkDecls (bagToList . tcdMeths) (ValD noExtField) class_
    sigs = mkDecls tcdSigs (SigD noExtField) class_
    ats = mkDecls tcdATs ((TyClD noExtField) . (FamDecl noExtField)) class_

conDeclDocs :: ConDecl GhcRn -> [(Name, [HsDocString], SrcSpan)]
conDeclDocs conDecl =
  map (\(L loc n) -> (n, maybe [] (\(L _ (WithHsDocIdentifiers doc _)) -> [doc]) $ con_doc conDecl, locA loc)) $
  getConNames conDecl

selectorDocs :: ConDecl GhcRn -> [(Name, [HsDocString], SrcSpan)]
selectorDocs con =
  case con_args con of
    RecCon (L _ flds) ->
      concatMap
        (\(L _ (ConDeclField _ fieldOccs _ mbDoc)) ->
           map
             (\(L loc f) ->
                ( foExt f
                , maybe [] (\(L _ (WithHsDocIdentifiers doc _)) -> [doc]) mbDoc
                , locA loc
                ))
             fieldOccs)
        flds
    _ -> []

subordinateNamesWithDocs :: [GenLocated SrcSpan (HsDecl GhcRn)] -> [(Name, [LHsDoc GhcRn], SrcSpan)]
subordinateNamesWithDocs =
  concatMap $ \(L span tyClDecl) ->
    case tyClDecl of
      -- classDeclDocs already yields [LHsDoc GhcRn]
      TyClD _ classDecl@ClassDecl {..} ->
        concatMap
          (\(L _ decl, docs) ->
              map (\name -> (name, docs, span)) $ getMainDeclBinder decl
          )
          (classDeclDocs classDecl)
      -- conDeclDocs / selectorDocs return [(Name,[HsDocString],SrcSpan)]
      -- Wrap HsDocString → LHsDoc GhcRn at this boundary
      TyClD _ DataDecl {..} ->
        let conv :: (Name, [HsDocString], SrcSpan) -> (Name, [LHsDoc GhcRn], SrcSpan)
            conv (n, ds, sp) = (n, map (\s -> noLocA (WithHsDocIdentifiers s mempty)) ds, sp)
        in concatMap
              (\(L _ con) ->
                map conv (conDeclDocs con) ++ map conv (selectorDocs con)
              )
              (dd_cons tcdDataDefn)
      InstD _ (DataFamInstD _ DataFamInstDecl {..}) ->
        let conv (n, ds, sp) = (n, map (\s -> noLocA (WithHsDocIdentifiers s mempty)) ds, sp)
        in map conv (concatMap (conDeclDocs . unLoc) (dd_cons (feqn_rhs dfid_eqn)))
      _ -> []

isUserLSig :: LSig GhcRn -> Bool
isUserLSig (L _ s) = case s of
  TypeSig{}    -> True
  ClassOpSig{} -> True
  _            -> False

getMainDeclBinder :: HsDecl GhcRn -> [IdP GhcRn]
getMainDeclBinder (TyClD _ d) = [tcdName d]
getMainDeclBinder (ValD _ bind) =
  case bind of
    FunBind { fun_id = L _ name } -> [name]
    PatBind { pat_lhs = pat }     -> collectPatBinders CollNoDictBinders pat
    _                             -> []
getMainDeclBinder (SigD _ d) = sigNameNoLoc d
getMainDeclBinder (ForD _ (ForeignImport _ name _ _)) = [unLoc name]
getMainDeclBinder (ForD _ ForeignExport {}) = []
getMainDeclBinder _ = []

sigNameNoLoc :: Sig GhcRn -> [IdP GhcRn]
sigNameNoLoc (TypeSig _ ns _) = map unLoc ns
sigNameNoLoc (ClassOpSig _ _ ns _) = map unLoc ns
sigNameNoLoc (PatSynSig _ ns _) = map unLoc ns
sigNameNoLoc (SpecSig _ n _ _) = [unLoc n]
sigNameNoLoc (InlineSig _ n _) = [unLoc n]
sigNameNoLoc (FixSig _ (FixitySig _ ns _)) = map unLoc ns
sigNameNoLoc _                         = []

clsInstDeclSrcSpan :: ClsInstDecl GhcPs -> SrcSpan
clsInstDeclSrcSpan ClsInstDecl {cid_poly_ty = ty} = locA (getLoc ty)
clsInstDeclSrcSpan (XClsInstDecl _) = UnhelpfulSpan (UnhelpfulOther (fsLit "XClsInstDecl"))

toHsDocString :: LHsDoc GhcRn -> HsDocString
toHsDocString (L _ d) =
  case d of
    WithHsDocIdentifiers s _idents -> s

toHsDocStrings :: [LHsDoc GhcRn] -> [HsDocString]
toHsDocStrings = map toHsDocString

hsDocsToDocH :: UnitState -> DynFlags -> GlobalRdrEnv -> [HsDocString] -> Doc Name
hsDocsToDocH unitState flags rdrEnv chunks =
  let docRdr =
        overIdentifier (\_ -> parseIdent flags)
        . _doc
        . parseParas Nothing
        . concatMap renderHsDocString
        $ chunks
  in rename unitState flags rdrEnv docRdr

parseIdent :: DynFlags -> String -> Maybe RdrName
parseIdent dflags str0 =
  case unP parseIdentifier $
         initParserState
           (mkParserOpts (extensionFlags dflags) (initDiagOpts dflags) [] False False False False)
           (stringToStringBuffer str0)
           (mkRealSrcLoc (mkFastString "<unknown file>") 0 0) of
    POk _ name -> Just (unLoc name)
    _          -> Nothing

type Doc id = DocH (ModuleName, OccName) id

dataTcOccs :: RdrName -> [RdrName]
dataTcOccs x =
  let str = occNameString (rdrNameOcc x)
  in [ mkRdrUnqual (mkVarOcc str)
     , mkRdrUnqual (mkDataOcc str)
     , mkRdrUnqual (mkTcOcc str)
     ]

rename :: UnitState -> DynFlags -> GlobalRdrEnv -> Doc RdrName -> Doc Name
rename unitState dflags gre = rn
  where
    rn d = case d of
      DocAppend a b -> DocAppend (rn a) (rn b)
      DocParagraph doc -> DocParagraph (rn doc)
      DocIdentifier x -> do
        -- Generate the choices for the possible kind of thing this
        -- is.
        let choices = dataTcOccs x
        -- Try to look up all the names in the GlobalRdrEnv that match
        -- the names.
        let names = concatMap (\r -> map gre_name (lookupGRE gre (LookupRdrName r AllRelevantGREs))) choices
        case names of
          -- We found no names in the env so we start guessing.
          [] ->
            case choices of
              [] -> DocMonospaced (DocString (showPprUnsafe (rdrNameOcc x)))
              -- There was nothing in the environment so we need to
              -- pick some default from what's available to us. We
              -- diverge here from the old way where we would default
              -- to type constructors as we're much more likely to
              -- actually want anchors to regular definitions than
              -- type constructor names (such as in #253). So now we
              -- only get type constructor links if they are actually
              -- in scope.
              a:_ -> outOfScope dflags a

          -- There is only one name in the environment that matches so
          -- use it.
          [a] -> DocIdentifier a
          -- But when there are multiple names available, default to
          -- type constructors: somewhat awfully GHC returns the
          -- values in the list positionally.
          a:b:_ | isTyConName a -> DocIdentifier a
                | otherwise -> DocIdentifier b

      DocWarning doc -> DocWarning (rn doc)
      DocEmphasis doc -> DocEmphasis (rn doc)
      DocBold doc -> DocBold (rn doc)
      DocMonospaced doc -> DocMonospaced (rn doc)
      DocUnorderedList docs -> DocUnorderedList (map rn docs)
      DocOrderedList docs -> DocOrderedList (map (\(i,d) -> (i, rn d)) docs)
      DocDefList list -> DocDefList [ (rn a, rn b) | (a, b) <- list ]
      DocCodeBlock doc -> DocCodeBlock (rn doc)
      DocIdentifierUnchecked x -> DocIdentifierUnchecked x
      DocModule lnk -> DocModule (fmap rn lnk)
      DocHyperlink l -> DocHyperlink (fmap rn l)
      DocPic str -> DocPic str
      DocMathInline str -> DocMathInline str
      DocMathDisplay str -> DocMathDisplay str
      DocAName str -> DocAName str
      DocProperty p -> DocProperty p
      DocExamples e -> DocExamples e
      DocEmpty -> DocEmpty
      DocString str -> DocString str
      DocHeader (Header l t) -> DocHeader $ Header l (rn t)
      DocTable t -> DocTable (rn <$> t)

-- | Wrap an identifier that's out of scope (i.e. wasn't found in
-- 'GlobalReaderEnv' during 'rename') in an appropriate doc. Currently
-- we simply monospace the identifier in most cases except when the
-- identifier is qualified: if the identifier is qualified then we can
-- still try to guess and generate anchors accross modules but the
-- users shouldn't rely on this doing the right thing. See tickets
-- #253 and #375 on the confusion this causes depending on which
-- default we pick in 'rename'.
outOfScope :: DynFlags -> RdrName -> Doc a
outOfScope _ x =
  case x of
    Unqual occ -> monospaced occ
    Qual mdl occ -> DocIdentifierUnchecked (mdl, occ)
    Orig _ occ -> monospaced occ
    Exact name -> monospaced name -- Shouldn't happen since x is out of scope
  where
    monospaced :: Outputable a => a -> Doc b
    monospaced a = DocMonospaced (DocString (showPprUnsafe a))

makeAnchorId :: String -> String
makeAnchorId [] = []
makeAnchorId (f:r) = escape isAlpha f ++ concatMap (escape isLegal) r
  where
    escape p c | p c = [c]
               | otherwise = '-' : show (ord c) ++ "-"
    isLegal ':' = True
    isLegal '_' = True
    isLegal '.' = True
    isLegal c = isAscii c && isAlphaNum c

ghcDL :: a -> GHC.Located a
ghcDL = noLoc
