{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StrictData #-}

module HaskellCodeExplorer.AST.TypecheckedSource
  ( ASTState(..)
  , Environment(..)
  , TypeError(..)
  , foldTypecheckedSource
  , mkIdentifierInfo
  , mkIdentifierOccurrence
  , mkType
  , removeOverlappingInterval
  ) where

import GHC.Core.TyCo.Rep (Scaled(..), scaledThing)
import GHC.Core.TyCon (tyConDataCons)
import GHC.Data.Bag (bagToList)
import GHC.Types.Basic (Origin(..))
import GHC.Core.Class (Class, classTyVars, className)
import Control.Monad (return, unless, void)
import Control.Monad.State.Strict (State, get, modify')
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap.Strict as IM
import qualified Data.IntervalMap.Strict as IVM
import GHC.Unit.State (UnitState)
import qualified Data.Map.Strict as M
import GHC.Core.ConLike (ConLike(..))
import GHC.Core.DataCon  (dataConWrapId)
import GHC.Core.PatSyn   (patSynBuilder)
import GHC.Core.Predicate
import GHC.Core.Type (mkVisFunTy, mkVisFunTyMany, splitForAllTyCoVars)
import Data.List (find, span)
import Data.Maybe (Maybe, fromMaybe, mapMaybe)
import GHC.Utils.Outputable (ppr, showSDocUnsafe)
import qualified Data.Set as S
import qualified Data.Text as T
import GHC.Types.Id
import GHC.Driver.Session (DynFlags)
import GHC.Core.Type    (mkVisFunTyMany) 
import GHC.Data.FastString (mkFastString)
import HaskellCodeExplorer.GhcUtils
import qualified HaskellCodeExplorer.Types as HCE
import GHC.Types.TyThing (TyThing(..))
import GHC.Core.DataCon (dataConTyCon, dataConRepType)
import GHC.Hs
  ( ABExport(..)
  , anchor
  , unXRec
  , NoExtField(..)
  , LIdP(..)
  , HsRecUpdField
  , noAnnSrcSpan
  , noLocA
  , getLocA
  , EpAnn(..)
  , locA
  , AmbiguousFieldOcc(..)
  , ApplicativeArg(..)
  , RecordPatSynField(..)
  , AbsBinds(..)
  , SrcSpanAnnA
  , HsWrap(..)
  , MatchGroupTc(..)
  , OverLitTc(..)
  , HsFieldBind(..)
  , XXExprGhcTc(..)
  , ArithSeqInfo(..)
  , FieldOcc(..)
  , GRHS(..)
  , GRHSs(..)
  , HsBindLR(..)
  , HsCmd(..)
  , HsCmdTop(..)
  , HsConDetails(..)
  , HsConPatDetails
  , HsExpr(..)
  , HsLocalBindsLR(..)
  , HsOverLit(..)
  , HsRecField(..)
  , HsRecFields(..)
  , HsTupArg(..)
  , HsValBindsLR(..)
  , HsValBindsLR(..)
  , LGRHS
  , LHsBindLR
  , LHsBinds
  , LHsCmd
  , LHsCmd
  , LHsCmdTop
  , LHsExpr
  , LHsRecField
  , LHsRecUpdField
  , LHsTupArg
  , LMatch
  , LPat
  , LStmtLR
  , Match(..)
  , XXPatGhcTc(..)
  , Match(..)
  , MatchGroup(..)
  , ParStmtBlock(..)
  , Pat(..)
  , RecFieldsDotDot(..)
  , PatSynBind(..)
  , StmtLR(..)
  , selectorAmbiguousFieldOcc
  , XRecordCon (..)
  , XRecordUpd (..)
  , XListPat (..)
  , XOverLit (..)
  , MatchGroup (..)
  , NHsValBindsLR (..)
  )
import GHC.Types.TypeEnv (TypeEnv, lookupTypeEnv)
import GHC.Hs.Extension (GhcPs, GhcRn, GhcTc)
import GHC.Types.Id (idType)
import GHC.Core.InstEnv
  ( ClsInst(..)
  , InstEnvs
  , instanceSig
  , is_dfun
  , lookupUniqueInstEnv
  )
import GHC.Types.Name (Name, nameOccName, nameUnique)
import Prelude hiding (span)
import GHC.Types.SrcLoc
   ( GenLocated(..)
   , getLoc
   , noLoc
   , RealSrcSpan(..)
   , isGoodSrcSpan
   , isOneLineSpan
   , Located
   , SrcSpan(..)
   , UnhelpfulSpanReason(..)
   , noSrcSpan
   , unLoc
   )
import GHC.Tc.Types.Evidence (HsWrapper(..))
import GHC.Core.ConLike (ConLike(..), conLikeResTy)
import GHC.Hs.Syn.Type (hsLitType, hsExprType)
import GHC.Core.TyCo.Compare (nonDetCmpTypes, eqTypes, eqType)
import GHC.Core.Type
  ( Type
  , mkFunTy
  , splitFunTy_maybe
  , splitFunTys
  , substTys
  , tidyOpenType
  , zipTvSubst
  )
import GHC.Types.Unique (getKey)
import GHC.Builtin.Types (mkListTy, mkTupleTy, manyDataConTy, manyDataCon)
import GHC.Types.Var (Id, Var, idDetails, isId, setVarName, setVarType, varName, varType)
import GHC.Types.Id.Info ( IdDetails(..))
import GHC.Types.Var.Env (TidyEnv)

data ASTState = ASTState
  { astStateExprInfoMap :: !HCE.ExpressionInfoMap
  -- ^ Type of each expression
  , astStateIdOccMap :: !HCE.IdentifierOccurrenceMap
  -- ^ Each occurrence of an identifier in a source code
  , astStateIdSrcSpanMap :: !(M.Map RealSrcSpan (Var, Maybe (Type, [Type])))
  -- ^ Intermediate data structure that is used to populate 'IdentifierOccurrenceMap'
  -- and 'IdentifierInfoMap'.
  -- 'SrcSpan' - location of an identifier in a source code
  -- 'Type' - 'expected' type of an identifier
  -- '[Type]' - types at which type variables are instantiated
  , astStateTidyEnv :: !TidyEnv
  -- ^ 'TidyEnv' is used to prevent name clashes of free type variables.
  -- ('TidyEnv' contains all free type variables in scope)
  , astStateHsWrapper :: !(Maybe HsWrapper)
  -- ^ HsWrapper comes from 'HsWrap' constructor of 'HsExpr' datatype.
  , astStateEnv :: !Environment
  -- ^ 'Environment' doesn't change
  , astStateTypeErrors :: [TypeError]
  -- ^ Non-empty list of TypeError's indicates that most likely there is a bug in
  -- a fold_something function in this module.
  }

-- | A 'TypeError' means that an assumption about a type of an AST node is incorrect.
data TypeError = TypeError
  { typeErrorSrcSpan :: SrcSpan
  , typeErrorMessage :: T.Text
  , typeErrorASTNodeName :: T.Text
  } deriving (Show, Eq)

data Environment = Environment
  { envDynFlags :: DynFlags
  , envUnitState :: UnitState
  , envTypeEnv :: TypeEnv
  , envInstEnv :: InstEnvs
  , envTransformation :: HCE.SourceCodeTransformation
  , envPackageId :: HCE.PackageId
  , envCurrentModuleDefSites :: HCE.DefinitionSiteMap
  , envFileMap :: HM.HashMap HCE.HaskellFilePath HCE.HaskellModulePath
  , envDefSiteMap :: HM.HashMap HCE.HaskellModulePath HCE.DefinitionSiteMap
  , envModuleNameMap :: HM.HashMap HCE.HaskellModuleName (HM.HashMap HCE.ComponentId HCE.HaskellModulePath)
  , envExportedNames :: S.Set Name
  , envComponentId :: HCE.ComponentId
  }

-- | Indicates whether an expression consists of more than one token.
-- Simple expression : wildcard, literal
-- Composite expression : application, lambda abstraction,...
data ExprSort
  = Simple
  | Composite
  deriving (Show, Eq)

exprSort :: HsExpr a -> ExprSort
exprSort HsVar {} = Simple
exprSort HsIPVar {} = Simple
exprSort HsOverLit {} = Simple
exprSort HsLit {} = Simple

exprSort (ExplicitTuple _ args _)
  | null args = Simple
  | otherwise = Composite
exprSort (ExplicitList _ args)
  | null args = Simple
  | otherwise = Composite
exprSort _ = Composite


patSort :: Pat a -> ExprSort
patSort WildPat {} = Simple
patSort LitPat {} = Simple
patSort NPat {} = Simple
patSort (ListPat _ pats)
  | null pats = Simple
  | otherwise = Composite
patSort (TuplePat  _ pats _)
  | null pats = Simple
  | otherwise = Composite
patSort _ = Composite

-- | Splits a type of a function, adds 'TypeError' to 'ASTState'
-- in case of failure.
splitFunTySafe ::
     SrcSpan -> T.Text -> Type -> State ASTState (Maybe (Type, Type))
splitFunTySafe srcSpan astNode typ =
  case splitFunTy_maybe typ of
    Just (_funTyFlag, _mult, ty1, ty2) -> return $ Just (ty1, ty2)
    Nothing -> do
      flags <- envDynFlags . astStateEnv <$> get
      let typeError =
            TypeError
              { typeErrorSrcSpan = srcSpan
              , typeErrorMessage = T.append "splitFunTy : " $ T.pack $ showSDocUnsafe (ppr typ)
              , typeErrorASTNodeName = astNode
              }
      modify'
        (\st -> st {astStateTypeErrors = typeError : astStateTypeErrors st})
      return Nothing

-- | Splits a type of a function of two arguments, adds
-- 'TypeError' to 'ASTState' in case of a failure.
splitFunTy2Safe ::
     SrcSpan -> T.Text -> Type -> State ASTState (Maybe (Type, Type, Type))
splitFunTy2Safe srcSpan astNode typ = do
  tys <- splitFunTySafe srcSpan astNode typ
  case tys of
    Just (arg1, ty1) -> do
      res <- splitFunTySafe srcSpan astNode ty1
      case res of
        Just (arg2, ty2) -> return $ Just (arg1, arg2, ty2)
        Nothing -> return Nothing
    Nothing -> return Nothing

-- | Returns result type of a function, adds 'TypeError' to
-- 'ASTState' in case of a failure.
funResultTySafe :: SrcSpan -> T.Text -> Type -> State ASTState (Maybe Type)
funResultTySafe srcSpan astNode typ =
  fmap snd <$> splitFunTySafe srcSpan astNode typ

-- | Returns result type of a function of two arguments,
-- adds 'TypeError' to 'ASTState' in case of a failure.
funResultTy2Safe :: SrcSpan -> T.Text -> Type -> State ASTState (Maybe Type)
funResultTy2Safe srcSpan astNode typ = do
  mbResTy1 <- funResultTySafe srcSpan astNode typ
  case mbResTy1 of
    Just resTy1 -> funResultTySafe srcSpan astNode resTy1
    Nothing -> return Nothing

addIdentifierToIdSrcSpanMap :: SrcSpan -> Id -> Maybe (Type, [Type]) -> State ASTState ()
addIdentifierToIdSrcSpanMap span identifier mbTypes
  | RealSrcSpan real _ <- span =
    modify' $ \astState@ASTState {astStateIdSrcSpanMap = ids} ->
      let ids' = M.insert real (identifier, mbTypes) ids
       in astState {astStateIdSrcSpanMap = ids'}
addIdentifierToIdSrcSpanMap _ _ _ = return ()

-- | Updates 'ExpressionInfoMap' or 'IdentifierOccurrenceMap' depending
-- on 'ExprSort'.
addExprInfo :: SrcSpan -> Maybe Type -> T.Text -> ExprSort -> State ASTState ()
addExprInfo span mbType descr sort = do
  transformation <- envTransformation . astStateEnv <$> get
  case srcSpanToLineAndColNumbers transformation span of
    Just (_file,(startLine, startCol), (endLine, endCol)) -> do
      flags <- envDynFlags . astStateEnv <$> get
      mbHsWrapper <- astStateHsWrapper <$> get
      modify' $ \astState@ASTState {astStateExprInfoMap = exprInfoMap} ->
        case sort of
          Composite ->
            let exprInfo =
                  HCE.ExpressionInfo
                    {exprType = mkType flags <$> mbType, description = descr}
                interval =
                  IVM.OpenInterval (startLine, startCol) (endLine, endCol)
                exprInfoMap' = IVM.insert interval exprInfo exprInfoMap
             in astState {astStateExprInfoMap = exprInfoMap'}
          Simple ->
            let idOcc =
                  HCE.IdentifierOccurrence
                    { internalId = Nothing
                    , internalIdFromRenamedSource = Nothing
                    , isBinder = False
                    , instanceResolution = Nothing
                    , idOccType =
                        case mbHsWrapper of
                          Just w -> mkType flags <$> (applyWrapper w <$> mbType)
                          Nothing -> mkType flags <$> mbType
                    , typeArguments = Nothing
                    , description = descr
                    , sort = HCE.ValueId
                    }
                idOccMap =
                  IM.insertWith
                    removeOverlappingInterval
                    startLine
                    [((startCol, endCol), idOcc)]
                    (astStateIdOccMap astState)
             in astState {astStateIdOccMap = idOccMap}
    Nothing -> return ()

-- | Finds the first interval that overlaps with a new interval
-- and adds the smaller one of the two to the list. If there are no overlapping
-- intervals then this function adds a new interval to the list.
removeOverlappingInterval ::
     forall a. [((Int, Int), a)] -> [((Int, Int), a)] -> [((Int, Int), a)]
removeOverlappingInterval [newInterval@((newStart, newEnd), _newVal)] intervals =
  go intervals False
  where
    go ::
         [((Int, Int), a)]
      -> Bool -- If an overlapping interval is found
      -> [((Int, Int), a)]
    go (i:is) True = i : go is True
    -- Current interval is inside new interval
    go (interval@((s, e), _val):is) False
      | newStart <= s && newEnd >= e = interval : go is True
    -- New interval is inside current interval
    go (((s, e), _val):is) False
      | newStart >= s && newEnd <= e = newInterval : go is True
    -- Intervals partially overlap
    go (interval@((s, e), _val):is) False
      | newStart >= s && newEnd >= e && newStart < e =
        (if e - s >= newEnd - newStart
           then newInterval
           else interval) :
        go is True
    -- Intervals partially overlap
    go (interval@((s, e), _val):is) False
      | newStart <= s && newEnd <= e && newEnd > s =
        (if e - s >= newEnd - newStart
           then newInterval
           else interval) :
        go is True
    -- Intervals don't overlap
    go (interval:is) False = interval : go is False
    go [] True = []
    go [] False = [newInterval]
removeOverlappingInterval _ intervals = intervals

newtype InstTypes = InstTypes [Type]

instance Eq InstTypes where
  (==) (InstTypes ts1) (InstTypes ts2) = eqTypes ts1 ts2

instance Ord InstTypes where
  compare (InstTypes ts1) (InstTypes ts2) = nonDetCmpTypes ts1 ts2

-- | Creates an instance resolution tree
traceInstanceResolution ::
     Environment
  -> Class
  -> [Type] -- ^ Types at which type variables of a class are instantated
  -> HCE.InstanceResolution
traceInstanceResolution environment c ts = go c ts S.empty
  where
    flags = envDynFlags environment
    go :: Class -> [Type] -> S.Set (Name, InstTypes) -> HCE.InstanceResolution
    go cls types seenInstances =
      let clsTyVarCount = length $ classTyVars cls
       in case lookupUniqueInstEnv
                 (envInstEnv environment)
                 cls
                 (take clsTyVarCount types) of
            Right (inst, instTypes) ->
              -- A successful match is a ClsInst, together with the types at which
              -- the dfun_id in the ClsInst should be instantiated
              let instWithTypes = (is_dfun_name inst, InstTypes instTypes)
               in if not $ S.member instWithTypes seenInstances
                    then let (typeVars, predTypes, _class, _types) =
                               instanceSig inst
                             subst = zipTvSubst typeVars instTypes
                             constraints =
                               mapMaybe getClassPredTys_maybe . substTys subst $
                               predTypes
                          in HCE.Instance
                               (instanceToText flags inst)
                               (mkType flags . idType $ is_dfun inst)
                               (map (mkType flags) instTypes)
                               (nameLocationInfo
                                (envUnitState environment) flags (envPackageId environment)
                                (envComponentId environment) (envTransformation environment)
                                (envFileMap environment) (envDefSiteMap environment)
                                (Just (instanceToText flags inst)) Nothing (varName (is_dfun inst)))
                               (map
                                  (\(cl, tys) ->
                                     go
                                       cl
                                       tys
                                       (S.insert instWithTypes seenInstances))
                                  constraints)
                    else HCE.Stop
            Left _ -> HCE.Stop

mkIdentifierInfo :: Environment -> Id -> Maybe Name -> HCE.IdentifierInfo
mkIdentifierInfo environment identifier mbNameFromRenamedSource =
  let name = fromMaybe (varName identifier) mbNameFromRenamedSource
      sort = nameSort name
      nameSpace = occNameNameSpace . nameOccName $ name
      flags = envDynFlags environment
      currentPackageId = envPackageId environment
      compId = envComponentId environment
      transformation = envTransformation environment
      fileMap = envFileMap environment
      defSiteMap = envDefSiteMap environment
      locationInfo =
        nameLocationInfo
          (envUnitState environment)
          flags
          currentPackageId
          compId
          transformation
          fileMap
          defSiteMap
          Nothing
          Nothing
          name
   in HCE.IdentifierInfo
        { sort = sort
        , occName = HCE.OccName $ nameToText name
        , demangledOccName = demangleOccName name
        , nameSpace = nameSpace
        , idType = mkType flags $ varType identifier
        , locationInfo = locationInfo
        , details = mbIdDetails identifier
        , doc =
            nameDocumentation
              transformation
              fileMap
              defSiteMap
              (envCurrentModuleDefSites environment)
              name
        , internalId = HCE.InternalId $ identifierKey flags identifier
        , externalId =
            case sort of
              HCE.External ->
                case locationInfo of
                  HCE.ExactLocation {..} ->
                    Just $
                    HCE.ExternalId $
                    T.intercalate
                      "|"
                      [ HCE.packageIdToText currentPackageId
                      , HCE.getHaskellModuleName moduleName
                      , case nameSpace of
                          HCE.VarName -> T.pack $ show HCE.Val
                          HCE.DataName -> T.pack $ show HCE.Val
                          _ -> T.pack $ show HCE.Typ
                      , nameToText name
                      ]
                  HCE.ApproximateLocation {name = n, ..} ->
                    Just $
                    HCE.ExternalId $
                    T.intercalate
                      "|"
                      [ HCE.packageIdToText packageId
                      , HCE.getHaskellModuleName moduleName
                      , T.pack $ show entity
                      , n
                      ]
                  _ -> Nothing
              _ -> Nothing
        , isExported = S.member name $ envExportedNames environment
        }

mkIdentifierOccurrence ::
     Environment
  -> Id
  -> Name
  -> Maybe (Type, [Type])
  -> Bool
  -> T.Text
  -> HCE.IdentifierOccurrence
mkIdentifierOccurrence environment identifier nameFromRenamedSource mbInstTypes isBinder descr =
  let flags = envDynFlags environment
      mbClass
        | isId identifier =
          case idDetails identifier of
            ClassOpId cls _ -> Just cls
            _ -> Nothing
        | otherwise = Nothing
      mbInstanceResolution =
        case (mbClass, mbInstTypes) of
          (Just cls, Just (_, ts)) ->
            Just $ traceInstanceResolution environment cls ts
          _ -> Nothing
   in HCE.IdentifierOccurrence
        (Just . HCE.InternalId . identifierKey flags $ identifier)
        (Just . HCE.InternalId . T.pack . show . getKey . nameUnique $ nameFromRenamedSource)
        isBinder
        mbInstanceResolution
        (mkType flags . fst <$> mbInstTypes)
        (map (mkType flags) . snd <$> mbInstTypes)
        descr
        (if isId identifier
           then HCE.ValueId
           else HCE.TypeId)

restoreTidyEnv :: (State ASTState) a -> (State ASTState) a
restoreTidyEnv action = do
  tidyEnv <- astStateTidyEnv <$> get
  res <- action
  modify' $ \s -> s {astStateTidyEnv = tidyEnv}
  return res

restoreHsWrapper :: (State ASTState) a -> (State ASTState) a
restoreHsWrapper action = do
  wrapper <- astStateHsWrapper <$> get
  res <- action
  modify' $ \s -> s {astStateHsWrapper = wrapper}
  return res

tidyIdentifier :: Id -> State ASTState (Id, Maybe (Type, [Type]))
tidyIdentifier identifier = do
  tidyEnv <- astStateTidyEnv <$> get
  mbHsWrapper <- astStateHsWrapper <$> get
  let (tidyEnv', identifier') = tidyIdentifierType tidyEnv identifier
      identifierType = varType identifier'
      (mbTypes, updatedEnv) =
        case mbHsWrapper of
          Just wrapper ->
            let expectedType = applyWrapper wrapper identifierType
                (tidyEnv'', expectedType') = tidyOpenType tidyEnv' expectedType
                wrapperTys =
                  map (snd . tidyOpenType tidyEnv'') (wrapperTypes wrapper)
             in if not $ eqType expectedType identifierType
                  then (Just (expectedType', wrapperTys), tidyEnv'')
                  else (Nothing, tidyEnv')
          Nothing -> (Nothing, tidyEnv')
  modify' (\s -> s {astStateTidyEnv = updatedEnv})
  return (identifier', mbTypes)

tidyType :: Type -> State ASTState Type
tidyType typ = do
  tidyEnv <- astStateTidyEnv <$> get
  let (tidyEnv', typ') = tidyOpenType tidyEnv typ
  modify' (\s -> s {astStateTidyEnv = tidyEnv'})
  return typ'

foldTypecheckedSource :: LHsBinds GhcTc -> State ASTState ()
foldTypecheckedSource = foldLHsBindsLR

foldLHsExpr :: LHsExpr GhcTc -> State ASTState (Maybe Type)
foldLHsExpr (L _span (XExpr _)) = return Nothing
foldLHsExpr (L _ (HsOverLit _ (XOverLit _))) = return Nothing
foldLHsExpr (L _ (HsLam _ _ (XMatchGroup _))) = return Nothing
foldLHsExpr (L _ (HsCase _ _ (XMatchGroup _))) = return Nothing
foldLHsExpr (L ann (HsVar _ identifierL)) =
  case identifierL of
    L loc identifier -> restoreTidyEnv $ do
      (identifier', mbTypes) <- tidyIdentifier identifier
      addIdentifierToIdSrcSpanMap (locA loc) identifier' mbTypes
      return . Just . varType $ identifier'
foldLHsExpr (L _ HsUnboundVar {}) = return Nothing
foldLHsExpr (L _ (XExpr (ConLikeTc con _ _))) =
  restoreTidyEnv $ do
    let mbType = case con of
          RealDataCon dc ->
            let tyCon = dataConTyCon dc
                dcs   = tyConDataCons tyCon
                mbId  = find (\d -> d == dc) dcs  -- or just use dc directly
            in Just (dataConRepType dc)
          PatSynCon ps   -> Just (varType $ patSynId ps)
    maybe (pure Nothing) (fmap Just . tidyType) mbType
foldLHsExpr (L _ (HsGetField  {})) = return Nothing
foldLHsExpr (L _ (HsProjection {})) = return Nothing
foldLHsExpr (L _ HsOverLabel {}) = return Nothing
foldLHsExpr (L ann expr@HsIPVar {}) = do
  addExprInfo (locA ann) Nothing "HsIPVar" (exprSort expr)
  return Nothing
foldLHsExpr (L ann (HsOverLit _ (OverLit (OverLitTc _ _ ol_type) _))) =
  restoreTidyEnv $ do
    typ <- tidyType ol_type
    let span = locA ann
    addExprInfo
      span
      (Just typ)
      "HsOverLit"
      (if isOneLineSpan span then Simple else Composite)
    return $ Just typ
foldLHsExpr (L ann (HsLit _ lit)) =
  restoreTidyEnv $ do
    typ <- tidyType $ hsLitType lit
    let span = locA ann
    addExprInfo
      span
      (Just typ)
      "HsLit"
      (if isOneLineSpan span then Simple else Composite)
    return $ Just typ
foldLHsExpr (L ann expr@(HsLam _ _ (MG (MatchGroupTc {..}) mg_alts))) =
  restoreTidyEnv $ do
    typ <- tidyType $
      foldr (\(Scaled m ty) acc -> mkVisFunTy m ty acc) mg_res_ty mg_arg_tys
    let span = locA ann
    addExprInfo span (Just typ) "HsLam" (exprSort expr)
    mapM_ foldLMatch $ unLoc mg_alts
    return $ Just typ
foldLHsExpr (L ann (HsApp ext fun arg)) = do
  funTy  <- foldLHsExpr fun
  _argTy <- foldLHsExpr arg
  let span = locA ann
      e    = HsApp ext fun arg
  typ <- maybe (return Nothing) (funResultTySafe span "HsApp") funTy
  addExprInfo span typ "HsApp" (exprSort e)
  return typ
foldLHsExpr (L ann e@(HsAppType ext expr arg)) = do
  typ <- foldLHsExpr expr
  let span = locA ann
  addExprInfo span typ "HsAppType" (exprSort e)
  return typ
foldLHsExpr (L ann e@(OpApp ext left op right)) = do
  opTyp <- foldLHsExpr op
  let span = locA ann
  typ <- maybe (return Nothing) (funResultTy2Safe span "OpApp") opTyp
  _ <- foldLHsExpr left
  _ <- foldLHsExpr right
  addExprInfo span typ "OpApp" (exprSort e)
  return typ
foldLHsExpr (L ann e@(NegApp _ expr _)) = do
  typ <- foldLHsExpr expr
  let span = locA ann
  addExprInfo span typ "NegApp" (exprSort e)
  return typ
foldLHsExpr (L _span (HsPar _ expr)) = foldLHsExpr expr
foldLHsExpr (L ann e@(SectionL ext operand operator)) = do
  opType <- foldLHsExpr operator
  _      <- foldLHsExpr operand
  let span = locA ann
  mbTypes <- maybe (return Nothing) (splitFunTy2Safe span "SectionL") opType
  let typ =
        case mbTypes of
          Just (_arg1, arg2, res) -> Just (mkVisFunTyMany arg2 res)
          Nothing                 -> Nothing
  addExprInfo span typ "SectionL" (exprSort e)  -- e 是裸 HsExpr
  return typ
foldLHsExpr (L ann e@(SectionR ext operator operand)) = do
  opType  <- foldLHsExpr operator
  _       <- foldLHsExpr operand
  let span = locA ann
  mbTypes <- maybe (return Nothing) (splitFunTy2Safe span "SectionR") opType
  let typ =
        case mbTypes of
          -- SectionR 固定了右参数，余下是 a -> res
          Just (arg1, _arg2, res) -> Just (mkVisFunTyMany arg1 res)
          -- 等价写法：Just (mkVisFunTy Many arg1 res)
          Nothing                 -> Nothing
  addExprInfo span typ "SectionR" (exprSort e)
  return typ
-- foldLHsExpr expr@(L spanA e@(ExplicitTuple _ tupArgs boxity)) = do
--   tupleArgs <- mapM foldLHsTupArg tupArgs
--   let sectionArgs = mapMaybe fst . filter ((== TupArgMissing) . snd) $ tupleArgs
--       argTys      = mapMaybe fst tupleArgs
--       resultType  = pure $ foldr mkVisFunTyMany (mkTupleTy boxity argTys) sectionArgs
--   tidyEnv <- astStateTidyEnv <$> get
--   addExprInfo
--     (getLocA expr)
--     (snd . tidyOpenType tidyEnv <$> resultType)
--     "ExplicitTuple"
--     (exprSort e)
--   pure resultType
foldLHsExpr (L _span (ExplicitSum _ _ _ expr)) = do
  -- TODO
  _ <- foldLHsExpr expr
  return Nothing
foldLHsExpr (L l e@(HsCase _ expr (MG (MatchGroupTc {..}) mg_alts))) =
  restoreTidyEnv $ do
    typ <- tidyType mg_res_ty
    _ <- foldLHsExpr expr
    mapM_ foldLMatch (unLoc mg_alts)
    addExprInfo (locA l) (Just typ) "HsCase" (exprSort e)
    return $ Just typ
foldLHsExpr expr@(L _ e@(HsIf _ condExpr thenExpr elseExpr)) = do
  _ <- foldLHsExpr condExpr
  typ <- foldLHsExpr thenExpr
  _ <- foldLHsExpr elseExpr
  addExprInfo (getLocA expr) typ "HsIf" (exprSort e)
  return typ
foldLHsExpr expr@(L _ e@(HsMultiIf typ grhss)) = restoreTidyEnv $ do
  typ' <- tidyType typ
  addExprInfo (getLocA expr) (Just typ') "HsMultiIf" (exprSort e)
  mapM_ foldLGRHS grhss
  return $ Just typ'
foldLHsExpr expr@(L _ e@(HsLet _ binds body)) = do
  _ <- foldHsLocalBindsLR binds
  typ <- foldLHsExpr body
  addExprInfo (getLocA expr) typ "HsLet" (exprSort e)
  return typ
foldLHsExpr expr@(L l (HsDo typ _context (L _ stmts))) =
  restoreTidyEnv $ do
    typ' <- tidyType typ
    addExprInfo (locA l) (Just typ') "HsDo" (exprSort (unLoc expr))
    mapM_ foldLStmtLR stmts
    return $ Just typ'
foldLHsExpr (L ann (ExplicitList typ exprs)) =
  restoreTidyEnv $ do
    typ' <- mkListTy <$> tidyType typ
    unless (null exprs) $ addExprInfo (locA ann) (Just typ') "ExplicitList" Composite
    mapM_ foldLHsExpr exprs
    return $ Just typ'
foldLHsExpr (L ann e@(RecordCon _ conExpr binds)) = do
    let conLikeP = unLoc conExpr
        mbConType = case conLikeP of
            RealDataCon dc -> Just (dataConRepType dc)
            _              -> Nothing
    addExprInfo (locA ann) mbConType "RecordCon" (exprSort e)
    _ <- foldHsRecFields binds
    return mbConType
-- TODO
-- foldLHsExpr (L ann (RecordUpd { rupd_expr = expr, rupd_flds = updFields })) = do
--   typ <- foldLHsExpr expr
--   addExprInfo (locA ann) typ "RecordUpd" (exprSort (RecordUpd expr updFields))
--   mapM_ foldLHsRecUpdField updFields
--   return typ
foldLHsExpr (L ann e@(ExprWithTySig _ expr _)) = do
  typ <- foldLHsExpr expr
  addExprInfo (locA ann) typ "ExprWithTySig" (exprSort e)
  return typ
foldLHsExpr (L ann e@(ArithSeq postTcExpr _mbSyntaxExpr seqInfo)) = do
  typ <-
    fmap (snd . splitFunTys . snd . splitForAllTyCoVars) <$>
    foldLHsExpr (L (noAnnSrcSpan (UnhelpfulSpan UnhelpfulNoLocationInfo)) postTcExpr)
  _ <-
    case seqInfo of
      From expr -> foldLHsExpr expr
      FromThen expr1 expr2 -> foldLHsExpr expr1 >> foldLHsExpr expr2
      FromTo expr1 expr2 -> foldLHsExpr expr1 >> foldLHsExpr expr2
      FromThenTo expr1 expr2 expr3 ->
        foldLHsExpr expr1 >> foldLHsExpr expr2 >> foldLHsExpr expr3
  addExprInfo (locA ann) typ "ArithSeq" (exprSort e)
  return typ
foldLHsExpr (L ann e@(HsPragE _ _ expr)) = do
  typ <- foldLHsExpr expr
  addExprInfo (locA ann) typ "HsPragE" (exprSort e)
  return typ
foldLHsExpr (L ann expr@(HsProc _ pat cmd)) = do
  _ <- foldLPat pat
  _ <- foldLHsCmdTop cmd
  addExprInfo (locA ann) Nothing "HsProc" (exprSort expr)
  return Nothing
foldLHsExpr (L ann e@(HsStatic _ expr)) = do
  typ <- foldLHsExpr expr
  addExprInfo (locA ann) typ "HsStatic" (exprSort e)
  return typ
foldLHsExpr (L l e@(XExpr (HsTick _ inner))) = do
  typ <- foldLHsExpr inner
  addExprInfo (locA l) typ "HsTick" (exprSort e)
  return typ
foldLHsExpr (L l e@(XExpr (HsBinTick _ _ inner))) = do
  typ <- foldLHsExpr inner
  addExprInfo (locA l) typ "HsBinTick" (exprSort e)
  return typ
foldLHsExpr (L span (XExpr (WrapExpr (HsWrap wrapper inner)))) =
  restoreHsWrapper $ do
    case exprSort inner of
      Simple    -> modify' (\s -> s {astStateHsWrapper = Just wrapper})
      Composite -> pure ()
    typ <- foldLHsExpr (L span inner)
    return $ applyWrapper wrapper <$> typ

foldHsRecFields :: HsRecFields GhcTc (LHsExpr GhcTc) -> State ASTState (Maybe Type)
foldHsRecFields HsRecFields {..} = do
  let userWritten =
        case rec_dotdot of
          Just x ->
            case unLoc x of
              RecFieldsDotDot n -> take n
          Nothing -> id
  mapM_ foldLHsRecField $ userWritten rec_flds
  return Nothing

foldLHsRecField :: LHsRecField GhcTc (LHsExpr GhcTc) -> State ASTState (Maybe Type)
foldLHsRecField (L _ (HsFieldBind { hfbLHS = L _ (XFieldOcc _) })) =
  return Nothing

foldLHsRecField (L ann (HsFieldBind { hfbLHS = L idAnn (FieldOcc identifier _)
                                    , hfbRHS = arg
                                    , hfbPun = pun })) =
  restoreTidyEnv $ do
    (identifier', mbTypes) <- tidyIdentifier identifier
    addIdentifierToIdSrcSpanMap (locA idAnn) identifier' mbTypes
    addExprInfo (locA ann) (Just . varType $ identifier') "HsRecField" Composite
    unless pun $ void (foldLHsExpr arg)
    return . Just . varType $ identifier'

-- TODO
-- foldLHsRecUpdField :: GenLocated SrcSpanAnnA (HsFieldBind (GenLocated SrcSpanAnnA (AmbiguousFieldOcc GhcTc)) (GenLocated SrcSpanAnnA (HsExpr GhcTc)))
--                    -> State ASTState (Maybe Type)
-- foldLHsRecUpdField (L span (HsFieldBind { hfbLHS = L idSpan recField
--                                         , hfbRHS = arg
--                                         , hfbPun = pun })) =
--   restoreTidyEnv $ do
--     let selectorId = selectorAmbiguousFieldOcc recField
--     (identifier', mbTypes) <- tidyIdentifier selectorId
--     -- Name of the selectorId is not 'correct' (Internal instead of External) :
--     -- https://github.com/ghc/ghc/blob/321b420f4582d103ca7b304867b916a749712e9f/compiler/typecheck/TcExpr.hs#L2424
--     typeEnv <- envTypeEnv . astStateEnv <$> get
--     let selName = varName selectorId
--         originalName =
--           case lookupTypeEnv typeEnv selName of
--             Just (AnId originalSelId) -> varName originalSelId
--             _ -> selName
--     let identifier'' = setVarName identifier' originalName
--     addIdentifierToIdSrcSpanMap idSpan identifier'' mbTypes
--     addExprInfo span (Just . varType $ identifier'') "HsRecUpdField" Composite
--     unless pun $ void (foldLHsExpr arg)
--     return . Just . varType $ identifier''

data TupArg
  = TupArgPresent
  | TupArgMissing
  deriving (Show, Eq)

foldLHsTupArg :: LHsTupArg GhcTc -> State ASTState (Maybe Type, TupArg)
foldLHsTupArg (L _span (XTupArg _)) = return (Nothing, TupArgMissing)
foldLHsTupArg (L _span (Present _ expr)) =
  restoreTidyEnv $ do
    typ <- foldLHsExpr expr
    typ' <-
      case typ of
        Just t -> Just <$> tidyType t
        Nothing -> return Nothing
    return (typ', TupArgPresent)
foldLHsTupArg (L _ (Missing typ)) =
  restoreTidyEnv $ do
    typ' <- tidyType (scaledThing typ)
    return (Just typ', TupArgMissing)

foldLMatch :: LMatch GhcTc (LHsExpr GhcTc) -> State ASTState (Maybe Type)
foldLMatch (L _span Match {..}) = do
  mapM_ foldLPat m_pats
  _ <- foldGRHSs m_grhss
  return Nothing
foldLMatch (L _span _) = return Nothing

foldLMatchCmd :: LMatch GhcTc (LHsCmd GhcTc) -> State ASTState (Maybe Type)
foldLMatchCmd (L _span Match {..}) = do
  mapM_ foldLPat m_pats
  _ <- foldGRHSsCmd m_grhss
  return Nothing
foldLMatchCmd (L _span _) = return Nothing

foldGRHSsCmd :: GRHSs GhcTc (LHsCmd GhcTc) -> State ASTState (Maybe Type)
foldGRHSsCmd GRHSs {..} = do
  mapM_ foldLGRHSCmd grhssGRHSs
  _ <- foldHsLocalBindsLR grhssLocalBinds
  return Nothing
foldGRHSsCmd (_) = return Nothing

foldGRHSs :: GRHSs GhcTc (LHsExpr GhcTc) -> State ASTState (Maybe Type)
foldGRHSs GRHSs {..} = do
  mapM_ foldLGRHS grhssGRHSs
  _ <- foldHsLocalBindsLR grhssLocalBinds
  return Nothing
foldGRHSs (_) = return Nothing

foldLStmtLR :: LStmtLR GhcTc GhcTc (LHsExpr GhcTc) -> State ASTState (Maybe Type)
foldLStmtLR (L _span (XStmtLR _)) = return Nothing
foldLStmtLR (L ann (LastStmt _ body _ _)) = do
  typ <- foldLHsExpr body
  addExprInfo (locA ann) typ "LastStmt" Composite
  return typ
foldLStmtLR (L _span (BindStmt _ pat body)) = do
  _ <- foldLPat pat
  _ <- foldLHsExpr body
  return Nothing
foldLStmtLR (L ann (BodyStmt _ body _ _)) = do
  mbTyp <- foldLHsExpr body
  addExprInfo (locA ann) mbTyp "BodyStmt" Composite
  return mbTyp
foldLStmtLR (L _ (LetStmt _ binds)) = do
  _ <- foldHsLocalBindsLR binds
  return Nothing
foldLStmtLR (L _ (ParStmt _ blocks _ _)) = do
  mapM_ foldParStmtBlock blocks
  return Nothing
foldLStmtLR (L _ TransStmt {..}) = do
  mapM_ foldLStmtLR trS_stmts
  _ <- maybe (return Nothing) foldLHsExpr trS_by
  _ <- foldLHsExpr trS_using
  return Nothing
foldLStmtLR (L _span RecStmt {..}) = do
  mapM_ foldLStmtLR (unLoc recS_stmts)
  return Nothing
foldLStmtLR (L ann (ApplicativeStmt typ args _)) =
  restoreTidyEnv $ do
    typ' <- tidyType typ
    mapM_ (foldApplicativeArg . snd) args
    addExprInfo (locA ann) (Just typ') "ApplicativeStmt" Composite
    return Nothing

foldApplicativeArg :: ApplicativeArg GhcTc -> State ASTState (Maybe Type)
foldApplicativeArg appArg =
  case appArg of
    XApplicativeArg _ -> return Nothing
    ApplicativeArgOne _ pat expr _bool -> do
      _ <- foldLPat pat
      _ <- foldLHsExpr expr
      return Nothing
    ApplicativeArgMany _ exprStmts _ pat _ -> do
      mapM_ foldLStmtLR exprStmts
      _ <- foldLPat pat
      return Nothing
foldLStmtLRCmd ::
     LStmtLR GhcTc GhcTc (LHsCmd GhcTc) -> State ASTState (Maybe Type)
foldLStmtLRCmd (L _ (XStmtLR _)) = return Nothing
foldLStmtLRCmd (L ann (LastStmt _ body _syntaxExpr _)) = do
  typ <- foldLHsCmd body
  addExprInfo (locA ann) typ "LastStmt Cmd" Composite
  return typ
foldLStmtLRCmd (L _ (BindStmt _ pat body)) = do
  _ <- foldLPat pat
  _ <- foldLHsCmd body
  return Nothing
foldLStmtLRCmd (L ann (BodyStmt _ body _ _)) = do
  typ <- foldLHsCmd body
  addExprInfo (locA ann) typ "BodyStmt Cmd" Composite
  return typ
foldLStmtLRCmd (L _ (LetStmt _ binds)) = do
  _ <- foldHsLocalBindsLR binds
  return Nothing
foldLStmtLRCmd (L _ (ParStmt _ blocks _ _)) = do
  mapM_ foldParStmtBlock blocks
  return Nothing
foldLStmtLRCmd (L _ TransStmt {..}) = do
  mapM_ foldLStmtLR trS_stmts
  _ <- foldLHsExpr trS_using
  _ <- maybe (return Nothing) foldLHsExpr trS_by
  return Nothing
foldLStmtLRCmd (L _ RecStmt {..}) = do
  mapM_ foldLStmtLRCmd (unLoc recS_stmts)
  return Nothing
foldLStmtLRCmd (L ann (ApplicativeStmt typ args _)) =
  restoreTidyEnv $ do
    typ' <- tidyType typ
    mapM_ (foldApplicativeArg . snd) args
    addExprInfo (locA ann) (Just typ') "ApplicativeStmt Cmd" Composite
    return Nothing

foldLGRHS :: LGRHS GhcTc (LHsExpr GhcTc) -> State ASTState (Maybe Type)
foldLGRHS (L _span (XGRHS _)) = return Nothing
foldLGRHS (L _span (GRHS _ guards body)) = do
  typ <- foldLHsExpr body
  mapM_ foldLStmtLR guards
  return typ

foldLGRHSCmd :: LGRHS GhcTc (LHsCmd GhcTc) -> State ASTState (Maybe Type)
foldLGRHSCmd (L _span (XGRHS _)) = return Nothing
foldLGRHSCmd (L _span (GRHS _ guards body)) = do
  typ <- foldLHsCmd body
  mapM_ foldLStmtLR guards
  return typ

foldParStmtBlock :: ParStmtBlock GhcTc GhcTc -> State ASTState (Maybe Type)
foldParStmtBlock (XParStmtBlock _) = return Nothing
foldParStmtBlock (ParStmtBlock _ exprStmts _ids _syntaxExpr) = do
  mapM_ foldLStmtLR exprStmts
  return Nothing

foldHsLocalBindsLR :: HsLocalBindsLR GhcTc GhcTc -> State ASTState (Maybe Type)
foldHsLocalBindsLR (XHsLocalBindsLR _) = return Nothing
foldHsLocalBindsLR (HsValBinds _ binds) = do
  _ <- foldHsValBindsLR binds
  return Nothing
foldHsLocalBindsLR HsIPBinds {} = return Nothing
foldHsLocalBindsLR EmptyLocalBinds {} = return Nothing

foldHsValBindsLR :: HsValBindsLR GhcTc GhcTc -> State ASTState (Maybe Type)

foldHsValBindsLR (ValBinds _ _binds _) = do
  return Nothing
foldHsValBindsLR (XValBindsLR (NValBinds binds _)) = do
  _ <- mapM_ (foldLHsBindsLR . snd) binds
  return Nothing

foldLHsBindsLR :: LHsBinds GhcTc -> State ASTState ()
foldLHsBindsLR = mapM_ (`foldLHsBindLR` Nothing) . bagToList

foldLHsBindLR :: LHsBindLR GhcTc GhcTc
              -> Maybe Id -- ^ Polymorphic id
              -> State ASTState (Maybe Type)
foldLHsBindLR (L _span (XHsBindsLR _)) _ = return Nothing
foldLHsBindLR (L _span (PatSynBind _ (XPatSynBind _))) _ = return Nothing
foldLHsBindLR (L _span FunBind { fun_id = funId0, fun_matches = matches }) mbPolyId
  | mg_origin (mg_ext matches) == FromSource =
    restoreTidyEnv $ do
      let funId :: LIdP GhcTc
          funId = funId0

          ident  = unLoc funId        -- :: Id
          idAnn  = getLocA funId
          typ    = maybe (varType ident) varType mbPolyId
          name   = maybe (varName ident) varName mbPolyId
          ident' = setVarType (setVarName ident name) typ
      (ident'', _) <- tidyIdentifier ident'
      addIdentifierToIdSrcSpanMap (locA idAnn) ident'' Nothing
      mapM_ foldLMatch (unLoc (mg_alts matches))
      return Nothing
  | otherwise = return Nothing
foldLHsBindLR (L _ PatBind {..}) _ = do
  _ <- foldLPat pat_lhs
  _ <- foldGRHSs pat_rhs
  return Nothing
foldLHsBindLR (L _ VarBind {..}) _ = return Nothing
-- TODO
-- foldLHsBindLR (L _ AbsBinds{ abs_exports, abs_binds }) = do
--   let polys :: [Id]
--       polys = map abe_poly abs_exports
--   mapM_ (\(b,i) -> foldLHsBindLR b (Just i))
--         (zip (bagToList abs_binds) polys)
--   return Nothing
-- foldLHsBindLR (L _ (PatSynBind _ PSB {..})) _ =
--   restoreTidyEnv $ do
--     _ <- foldLPat psb_def
--     _ <-
--       let addId :: LIdP GhcTc -> State ASTState ()
--           addId (L l i) = do
--             (i', _) <- tidyIdentifier i
--             addIdentifierToIdSrcSpanMap (locA l) i' Nothing
--        in case psb_args of
--             InfixCon id1 id2      -> addId id1 >> addId id2
--             PrefixCon _tyArgs ids -> mapM_ addId ids
--             RecCon recs ->
--               mapM_
--                 (\(RecordPatSynField selId patVar) ->
--                   addId (L (getFieldOccAnn selId) (foExt selId)) >> addId patVar)
--                 recs
--     return Nothing

foldLPat :: LPat GhcTc -> State ASTState (Maybe Type)
foldLPat (L _span (XPat _)) = return Nothing
foldLPat (L _ (NPat _ (L _ (XOverLit _)) _ _)) = return Nothing
foldLPat (L _ (NPlusKPat _ (L _ _) (L _ (XOverLit _)) _ _ _)) = return Nothing
foldLPat (L span (VarPat _ (L _ identifier))) = do
  (identifier', _) <- tidyIdentifier identifier
  addIdentifierToIdSrcSpanMap (locA span) identifier' Nothing
  return . Just . varType $ identifier'
foldLPat (L spanAnn pat@(WildPat typ)) = do
  typ' <- tidyType typ
  addExprInfo (locA spanAnn) (Just typ') "WildPat" (patSort pat)
  return $ Just typ'
foldLPat (L span p@(LazyPat _ pat)) = do
  mbType <- foldLPat pat
  addExprInfo (locA span) mbType "LazyPat" (patSort p)
  return mbType
foldLPat (L span p@(AsPat _ (L idAnn identifier) pat)) = do
  (identifier', _) <- tidyIdentifier identifier
  addIdentifierToIdSrcSpanMap (locA idAnn) identifier' Nothing
  addExprInfo (locA span) (Just . varType $ identifier') "AsPat" (patSort p)
  _ <- foldLPat pat
  return . Just . varType $ identifier'
foldLPat (L _span (ParPat _ pat)) = foldLPat pat
foldLPat (L span p@(BangPat _ pat)) = do
  typ <- foldLPat pat
  addExprInfo (locA span) typ "BangPat" (patSort p)
  return typ
-- foldLPat (L span p@(ListPat xlistPat pats)) = do
--   let typ = extractTypeFromXListPat xlistPat  -- You’ll need to define this
--   typ' <- tidyType typ
--   let listType = mkListTy typ'
--   addExprInfo span (Just listType) "ListPat" (patSort p)
--   mapM_ foldLPat pats
--   return $ Just listType
foldLPat (L spanAnn pat@(TuplePat types pats boxity)) = do
  typ' <- tidyType $ mkTupleTy boxity types
  addExprInfo (locA spanAnn) (Just typ') "TuplePat" (patSort pat)
  mapM_ foldLPat pats
  return $ Just typ'
foldLPat (L _span (SumPat _ pat _ _)) = do
  -- TODO
  _ <- foldLPat pat
  return Nothing
-- foldLPat (L span pat@ConPat {..}) = do
--   let (L idSpan conLike) = pat_con
--       conId =
--         case conLike of
--           RealDataCon dc -> dataConWorkId dc
--           PatSynCon ps -> patSynId ps
--       typ = conLikeResTy (unLoc pat_con) pat_arg_tys
--   (identifier', mbTypes) <- tidyIdentifier conId
--   addIdentifierToIdSrcSpanMap idSpan identifier' mbTypes
--   typ' <- tidyType typ
--   addExprInfo span (Just typ') "ConPat" (patSort pat)
--   _ <- foldHsConPatDetails pat_args
--   return . Just . varType $ identifier'
foldLPat (L span p@(ViewPat typ expr pat)) = do
  typ' <- tidyType typ
  addExprInfo (locA span) (Just typ') "ViewPat" (patSort p)
  _ <- foldLPat pat
  _ <- foldLHsExpr expr
  return $ Just typ'
foldLPat (L _ SplicePat {}) = return Nothing
foldLPat (L spanAnn (LitPat _ hsLit)) = do
  typ' <- tidyType $ hsLitType hsLit
  let span = locA spanAnn
  addExprInfo
    span
    (Just typ')
    "LitPat"
    (if isOneLineSpan span then Simple else Composite)
  return $ Just typ'
foldLPat (L span pat@(NPat _ (L _spanLit (OverLit (OverLitTc {..}) _)) _ _)) = do
  typ' <- tidyType ol_type
  addExprInfo (locA span) (Just typ') "NPat" (patSort pat)
  return $ Just ol_type
foldLPat (L spanAnn pat@(NPlusKPat typ (L idAnn identifier) (L litSpanAnn (OverLit (OverLitTc {..}) _)) _ _ _)) = do
  (identifier', _) <- tidyIdentifier identifier
  addIdentifierToIdSrcSpanMap (locA idAnn) identifier' Nothing
  typ' <- tidyType typ
  let span = locA spanAnn
  addExprInfo span (Just typ') "NPlusKPat" (patSort pat)
  olType' <- tidyType ol_type
  addExprInfo
    (locA litSpanAnn)
    (Just olType')
    "NPlusKPat"
    (if isOneLineSpan span then Simple else Composite)
  return $ Just typ'
foldLPat (L _span (SigPat typ pat _)) = do 
  typ' <- tidyType typ
  _ <- foldLPat pat
  return $ Just typ'
foldLPat (L spanAnn pat@(XPat (CoPat _ innerPat typ))) = do
  typ' <- tidyType typ
  let span = locA spanAnn
  addExprInfo span (Just typ') "CoPat" (patSort pat)
  _ <- foldLPat (L (noAnnSrcSpan span) innerPat)
  return Nothing
foldLPat _ = return Nothing

foldHsConPatDetails
  :: HsConPatDetails GhcTc
  -> State ASTState (Maybe Type)
foldHsConPatDetails (PrefixCon args _) = do
  -- mapM_ foldLPat args
  return Nothing
foldHsConPatDetails (RecCon rec) = do
  _ <- foldHsRecFieldsPat rec
  return Nothing
foldHsConPatDetails (InfixCon arg1 arg2) = do
  _ <- foldLPat arg1
  _ <- foldLPat arg2
  return Nothing

foldHsRecFieldsPat :: HsRecFields GhcTc (LPat GhcTc) -> State ASTState (Maybe Type)
foldHsRecFieldsPat HsRecFields {..} = do
  let onlyUserWritten =
        case rec_dotdot of
          Just (L _ (RecFieldsDotDot n)) -> take n
          Nothing -> id
  mapM_ foldLHsRecFieldPat $ onlyUserWritten rec_flds
  return Nothing

foldLHsRecFieldPat (L _ HsFieldBind
   { hfbLHS = L idAnn (FieldOcc identifier _)
   , hfbRHS = arg
   , hfbPun = pun
   }) = do
   let idSpan = locA idAnn
   (identifier', mbTypes) <- tidyIdentifier identifier
   addIdentifierToIdSrcSpanMap idSpan identifier' mbTypes
   unless pun $ void $ foldLPat arg
   return . Just . varType $ identifier'
foldLHsRecFieldPat (L _ HsFieldBind
   { hfbLHS = L _ (XFieldOcc _) }) =
   return Nothing

foldLHsCmdTop :: LHsCmdTop GhcTc -> State ASTState (Maybe Type)
foldLHsCmdTop (L _span (XCmdTop _)) = return Nothing
foldLHsCmdTop (L ann (HsCmdTop _ cmd)) = do
  mbTyp <- foldLHsCmd cmd
  addExprInfo (locA ann) mbTyp "HsCmdTop" Composite
  return mbTyp

foldLHsCmd :: LHsCmd GhcTc -> State ASTState (Maybe Type)
foldLHsCmd (L _ (XCmd _)) = return Nothing
foldLHsCmd (L _ (HsCmdLam _ _ (XMatchGroup _))) = return Nothing
foldLHsCmd (L _ (HsCmdCase _ _ (XMatchGroup _))) = return Nothing
foldLHsCmd (L _ (HsCmdArrApp _ expr1 expr2 _ _)) = do
  _ <- foldLHsExpr expr1
  _ <- foldLHsExpr expr2
  return Nothing
foldLHsCmd (L _ (HsCmdArrForm _ expr _  _ topCmds)) = do
  _ <- foldLHsExpr expr
  mapM_ foldLHsCmdTop topCmds
  return Nothing
foldLHsCmd (L _ (HsCmdApp _ cmd expr)) = do
  _ <- foldLHsCmd cmd
  _ <- foldLHsExpr expr
  return Nothing
foldLHsCmd (L _ (HsCmdLam _ _ MG {..})) = do
  mapM_ foldLMatchCmd $ unLoc mg_alts
  return Nothing
foldLHsCmd (L _ (HsCmdCase _ expr MG {..})) = do
  _ <- foldLHsExpr expr
  mapM_ foldLMatchCmd $ unLoc mg_alts
  return Nothing
foldLHsCmd (L _ (HsCmdPar _ cmd)) = do
  _ <- foldLHsCmd cmd
  return Nothing
foldLHsCmd (L _ (HsCmdIf _ _ expr cmd1 cmd2)) = do
  _ <- foldLHsCmd cmd1
  _ <- foldLHsCmd cmd2
  _ <- foldLHsExpr expr
  return Nothing
-- foldLHsCmd (L _ (HsCmdLet _ (L _ binds) cmd)) = do
--   _ <- foldLHsCmd cmd
--   _ <- foldHsLocalBindsLR binds
--   return Nothing
foldLHsCmd (L _ (HsCmdDo _ stmts)) = do
  mapM_ foldLStmtLRCmd $ unLoc stmts
  return Nothing
-- foldLHsCmd (L span (HsCmd _ _ cmd)) = do
  -- _ <- foldLHsCmd (L span cmd)
  -- return Nothing
