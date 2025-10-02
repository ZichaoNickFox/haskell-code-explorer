{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE StrictData #-}

module HaskellCodeExplorer.AST.RenamedSource
  ( NameOccurrence(..)
  , namesFromRenamedSource
  ) where
import GHC.Types.Var (Specificity(..))
import GHC.Types.Basic (TupleSort(..))
import GHC.Data.BooleanFormula (BooleanFormula(..))
import GHC.Builtin.Types (naturalTy, typeSymbolKind)
import GHC.TypeLits (Nat, Symbol)
import Language.Haskell.Syntax.Type
import Data.List.NonEmpty (toList)
import qualified GHC.Data.Strict as Strict
import GHC.Hs.Pat (HsRecField(..), hfbLHS, HsFieldBind(..))
import Data.Generics (Data, everything, extQ, mkQ)
import Data.Maybe (Maybe(..), mapMaybe)
import GHC.Hs.Expr (HsBracketTc(..), HsExpr(..), HsQuote(..))
import GHC.Hs.Type (HsTyVarBndr(..), HsConDetails(..))
import qualified Data.Text as T (Text)
import GHC
  ( AmbiguousFieldOcc(..)
  , getLocA
  , IdP
  , recordPatSynPatVar
  , unXRec
  , FunDep(..)
  , anchor
  , LIdP
  , NameAnn
  , ConDecl(..)
  , ConDeclField(..)
  , FamilyDecl(..)
  , EpAnn
  , XRec
  , FieldOcc(..)
  , FixitySig(..)
  , ForeignDecl(..)
  , GenLocated(..)
  , HsBindLR(..)
  , HsExpr(..)
  , HsPatSynDetails
  , HsRecField(..)
  , HsTupleSort(..)
  , HsTyLit(..)
  , HsTyVarBndr(..)
  , HsType(..)
  , IE(..)
  , LHsBindLR
  , LHsExpr
  , LHsTyPat
  , LHsType
  , locA
  , LPat
  , LSig
  , LTyClDecl
  , Located
  , HsMatchContext(..)
  , Match(..)
  , MatchGroup(..)
  , Name
  , Pat(..)
  , PatSynBind(..)
  , Sig(..)
  , TyClDecl(..)
  , FamEqn(..)
  , HsDataDefn(..)
  , Type
  , RoleAnnotDecl(..)
  , InjectivityAnn (..)
  , unLoc
  )
import GHC.Hs.Extension (GhcRn)
import HaskellCodeExplorer.GhcUtils (hsPatSynDetails, ieLocNames, ghcDL)
import Prelude hiding (span)
import GHC.Builtin.Types
  ( nilDataConName
  , tupleTyConName
  )
import GHC.Types.SrcLoc
  ( getLoc
  , mkRealSrcSpan
  , noSrcSpan
  , mkRealSrcLoc
  , realSrcSpanEnd
  , realSrcSpanStart
  , srcLocCol
  , srcLocFile
  , srcLocLine
  , SrcSpan(..)
  )
data NameOccurrence
  = NameOccurrence { locatedName :: Located (Maybe Name)
                   , description :: T.Text
                   , isBinder :: Bool }
  | TyLitOccurrence { locatedName :: Located (Maybe Name)
                    , description :: T.Text
                    , kind :: Type }

-- | Here we are only interested in a small subset of all AST nodes, so it is
-- convenient to use generic functions
namesFromRenamedSource :: (Data a) => a -> [NameOccurrence]
namesFromRenamedSource =
  everything
    (++)
    ([] `mkQ` hsExprNames `extQ` matchGroupNames `extQ` bindNames `extQ`
     patNames `extQ`
     sigNames `extQ`
     hsTypeNames `extQ`
     tyClDeclNames `extQ`
     familyDeclNames `extQ`
     familyEqNames `extQ`
     dataEqNames `extQ`
     conDeclNames `extQ`
     importNames `extQ`
     hsTyVarBndrNames `extQ`
     hsPatSynDetailsNames `extQ`
     conDeclFieldNames `extQ`
     hsRecFieldExprNames `extQ`
     hsRecAmbFieldExprNames `extQ`
     hsRecFieldPatNames `extQ`
     foreignDeclNames `extQ`
     roleAnnotationNames `extQ`
     injectivityAnnotationNames)

fieldOccName :: Bool -> FieldOcc GhcRn -> NameOccurrence
fieldOccName isBinder FieldOcc{ foExt = name, foLabel = L ann _rdr } =
  let span' = locA ann
  in NameOccurrence
       { locatedName = L span' (Just name)
       , description = "FieldOcc"
       , isBinder = isBinder
       }

conDeclFieldNames :: ConDeclField GhcRn -> [NameOccurrence]
conDeclFieldNames ConDeclField {..} =
  map (fieldOccName True . unLoc) cd_fld_names
conDeclFieldNames _ = []

hsRecFieldExprNames :: HsFieldBind (XRec GhcRn (FieldOcc GhcRn)) (LHsExpr GhcRn) -> [NameOccurrence]
hsRecFieldExprNames f = [ fieldOccName False (unLoc (hfbLHS f)) ]

hsRecAmbFieldExprNames
  :: HsFieldBind (XRec GhcRn (AmbiguousFieldOcc GhcRn)) (LHsExpr GhcRn)
  -> [NameOccurrence]
hsRecAmbFieldExprNames f =
  let spanA = getLocA (hfbLHS f)
  in [ NameOccurrence
        { locatedName = L spanA (Nothing :: Maybe Name)
        , description = "AmbiguousFieldOcc"
        , isBinder    = False
        }
     ]

hsRecFieldPatNames :: HsFieldBind (XRec GhcRn (FieldOcc GhcRn)) (LPat GhcRn) -> [NameOccurrence]
hsRecFieldPatNames f = [fieldOccName False $ unLoc (hfbLHS f)]

hsExprNames :: LHsExpr GhcRn -> [NameOccurrence]
hsExprNames (L _ (HsVar _ lname)) =
  let span' = locA (getLoc lname)   -- SrcSpanAnnN -> SrcSpan
      n     = unLoc lname           -- Name
  in [ NameOccurrence
        { locatedName = L span' (Just n)  -- Located (Maybe Name) with SrcSpan
        , description = "HsVar"
        , isBinder    = False
        }
     ]
hsExprNames (L spanA (ExplicitList _ exprs))
  | null exprs =
      [ NameOccurrence
          { locatedName = L (locA spanA) (Just nilDataConName)
          , description = "ExplicitList"
          , isBinder    = False
          }
      ]
  | otherwise = []
hsExprNames (L _ (RecordCon _ conLike _)) =
  let span' = locA (getLoc conLike)     -- :: SrcSpan
      n     = unLoc conLike             -- :: Name (ConLikeP GhcRn ~ Name at GhcRn)
  in [ NameOccurrence
        { locatedName = L span' (Just n)
        , description = "RecordCon"
        , isBinder    = False
        }
     ]
hsExprNames (L spanA (HsUntypedBracket _ (VarBr _ quote (L _ name)))) =
  case locA spanA of
    RealSrcSpan realSpan _ ->
      let start  = realSrcSpanStart realSpan
          end    = realSrcSpanEnd   realSpan
          offset = if quote then 1 else 2
          start' = mkRealSrcLoc (srcLocFile start)
                                (srcLocLine start)
                                (srcLocCol  start + offset)
          span'  = RealSrcSpan (mkRealSrcSpan start' end) Strict.Nothing
      in [ NameOccurrence
             { locatedName = L span' (Just name)
             , description = "VarBr"
             , isBinder    = False
             }
         ]
    _ -> []
hsExprNames _ = []

matchGroupNames :: MatchGroup GhcRn (LHsExpr GhcRn) -> [NameOccurrence]
matchGroupNames =
  mapMaybe (fmap toNameOcc . matchContextName . m_ctxt . unLoc) .
  unLoc . mg_alts
  where
    matchContextName :: HsMatchContext (LIdP GhcRn) -> Maybe (GenLocated (EpAnn NameAnn) Name)
    matchContextName (FunRhs name _ _) = Just name
    matchContextName _ = Nothing

    toNameOcc :: GenLocated (EpAnn NameAnn) Name -> NameOccurrence
    toNameOcc n =
      let span = locA n
          name = unLoc n
      in NameOccurrence
           { locatedName = Just <$> L span name
           , description = "Match"
           , isBinder = True
           }

bindNames :: LHsBindLR GhcRn GhcRn -> [NameOccurrence]
bindNames (L _span (PatSynBind _ PSB {..})) =
  let span = locA psb_id
      name = unLoc psb_id
   in [ NameOccurrence
          { locatedName = L span (Just name)
          , description = "PatSynBind"
          , isBinder = True
          }
      ]
bindNames _ = []

hsPatSynDetailsNames :: HsPatSynDetails GhcRn -> [NameOccurrence]
hsPatSynDetailsNames details =
  let mkNameOccurrence (L l n) =
        NameOccurrence
          { locatedName = L (locA l) (Just n)
          , description = "HsPatSynDetails"
          , isBinder    = True
          }
  in case details of
       PrefixCon _ names -> map mkNameOccurrence names            -- names :: [LIdP GhcRn]
       InfixCon n1 n2    -> map mkNameOccurrence [n1, n2]        -- n1,n2 :: LIdP GhcRn
       RecCon fields     -> map (mkNameOccurrence . recordPatSynPatVar) fields
                              -- recordPatSynPatVar :: RecordPatSynField GhcRn -> LIdP GhcRn

importNames :: IE GhcRn -> [NameOccurrence]
importNames =
  map toNameOcc . ieLocNames
  where
    toNameOcc :: LIdP GhcRn -> NameOccurrence
    toNameOcc lid =
      let span = locA lid
          name = unLoc lid
       in NameOccurrence
            { locatedName = L span (Just name)
            , description = "IE"
            , isBinder = False
            }

patNames :: LPat GhcRn -> [NameOccurrence]
patNames (L _span (VarPat _ (L _ name))) =
  [ NameOccurrence
    { locatedName = L noSrcSpan (Just name)
    , description = "VarPat"
    , isBinder = True
    }
  ]
patNames (L _span (ConPat _ (L _ name) _)) =
  [ NameOccurrence
    { locatedName = L noSrcSpan (Just name)
    , description = "ConPat"
    , isBinder = False
    }
  ]
patNames (L _span (AsPat _ (L ann name) _)) =
  [ NameOccurrence
      { locatedName = L (locA ann) (Just name)
      , description = "AsPat"
      , isBinder = True
      }
  ]
patNames (L _span (NPlusKPat _ (L ann name) _ _ _ _)) =
  [ NameOccurrence
      { locatedName = L (locA ann) (Just name)
      , description = "NPlusKPat"
      , isBinder = True
      }
  ]
patNames _ = []

sigNames :: LSig GhcRn -> [NameOccurrence]
sigNames (L _span (TypeSig _ names _)) =
  map
    (\(L ann name) ->
        NameOccurrence
          { locatedName = L (locA ann) (Just name)
          , description = "TypeSig"
          , isBinder = False
          })
    names
sigNames (L _span (PatSynSig _ names _)) =
  map
    (\(L ann name) ->
        NameOccurrence
          { locatedName = L (locA ann) (Just name)
          , description = "PatSynSig"
          , isBinder = False
          })
    names
sigNames (L _span (ClassOpSig _ _ names _)) =
  map
    (\(L ann name) ->
        NameOccurrence
          { locatedName = L (locA ann) (Just name)
          , description = "ClassOpSig"
          , isBinder = True
          })
    names
sigNames (L _span (FixSig _ (FixitySig _ names _))) =
  map
    (\(L ann name) ->
        NameOccurrence
          { locatedName = L (locA ann) (Just name)
          , description = "FixitySig"
          , isBinder = False
          })
    names
sigNames (L _span (InlineSig _ (L ann name) _)) =
  [ NameOccurrence
      { locatedName = L (locA ann) (Just name)
      , description = "InlineSig"
      , isBinder = False
      }
  ]
sigNames (L _span (SpecSig _ (L ann n) _ _)) =
  [ NameOccurrence
      { locatedName = L (locA ann) (Just n)
      , description = "SpecSig"
      , isBinder = False
      }
  ]
sigNames (L _span (MinimalSig _ (L _ boolFormula))) =
  map
    (\(L ann name) ->
        NameOccurrence
          { locatedName = L (locA ann) (Just name)
          , description = "MinimalSig"
          , isBinder = False
          })
    (boolFormulaNames boolFormula)
  where
    boolFormulaNames :: BooleanFormula (LIdP GhcRn) -> [LIdP GhcRn]
    boolFormulaNames (Var a) = [a]
    boolFormulaNames (And fs) = concatMap (boolFormulaNames . unLoc) fs
    boolFormulaNames (Or fs) = concatMap (boolFormulaNames . unLoc) fs
    boolFormulaNames (Parens (L _ f)) = boolFormulaNames f
sigNames (L _ _) = []

hsTypeNames :: LHsType GhcRn -> [NameOccurrence]
hsTypeNames (L _span (HsTyVar _ _promoted (L ann n))) =
  [ NameOccurrence
      { locatedName = L (locA ann) (Just n)
      , description = "HsTyVar"
      , isBinder = False
      }
  ]
hsTypeNames (L ann (HsTyLit _ lit)) =
  let kind =
        case lit of
          HsNumTy _ _ -> naturalTy
          HsStrTy _ _ -> typeSymbolKind
  in [ TyLitOccurrence
       { locatedName = L (locA ann) Nothing
       , description = "HsTyLit"
       , kind = kind
       }
     ]
hsTypeNames (L _span (HsOpTy _ _ _ (L ann name) _)) =
  [ NameOccurrence
      { locatedName = L (locA ann) (Just name)
      , description = "HsOpTy"
      , isBinder = False
      }
  ]
hsTypeNames (L ann (HsTupleTy _ hsTupleSort types))
  | null types =
    let tupleSort :: TupleSort
        tupleSort = case hsTupleSort of
          HsUnboxedTuple  -> UnboxedTuple
          _               -> BoxedTuple
    in [ NameOccurrence
         { locatedName = L (locA ann) (Just $ tupleTyConName tupleSort 0)
         , description = "HsTupleTy"
         , isBinder = False
         }
       ]
  | otherwise = []
--https://ghc.haskell.org/trac/ghc/ticket/13737
--hsTypeNames (L span (HsExplicitListTy _kind types)) = ...
--hsTypeNames (L span (HsExplicitTupleTy _kind types)) = ...
hsTypeNames _ = []

hsTyVarBndrNames :: HsTyVarBndr Specificity GhcRn -> [NameOccurrence]
hsTyVarBndrNames (UserTyVar _ _ n) =
  [ NameOccurrence
      { locatedName = L (getLocA n) (Just (unLoc n))
      , description = "UserTyVar"
      , isBinder    = True
      }
  ]
hsTyVarBndrNames (KindedTyVar _ _ n _) =
  [ NameOccurrence
      { locatedName = L (getLocA n) (Just (unLoc n))
      , description = "KindedTyVar"
      , isBinder    = True
      }
  ]
hsTyVarBndrNames _ = []

tyClDeclNames :: LTyClDecl GhcRn -> [NameOccurrence]
tyClDeclNames (L _span DataDecl {..}) =
  [ NameOccurrence
      { locatedName = L (locA (getLoc tcdLName)) (Just (unLoc tcdLName))
      , description = "DataDecl"
      , isBinder    = True
      }
  ]
tyClDeclNames (L _span SynDecl {..}) =
  [ NameOccurrence
      { locatedName = L (locA (getLoc tcdLName)) (Just (unLoc tcdLName))
      , description = "SynDecl"
      , isBinder    = True
      }
  ]
tyClDeclNames (L _span ClassDecl {..}) =
  NameOccurrence
    { locatedName = L (locA (getLoc tcdLName)) (Just (unLoc tcdLName))
    , description = "ClassDecl"
    , isBinder    = True
    }
  : concatMap
      (\fd -> case unLoc fd of
                FunDep _ lhs rhs ->
                  map toNameOcc lhs ++ map toNameOcc rhs)
      tcdFDs
  where
    toNameOcc :: LIdP GhcRn -> NameOccurrence
    toNameOcc n =
      NameOccurrence
        { locatedName = L (locA (getLoc n)) (Just (unLoc n))
        , description = "FunDep"
        , isBinder    = False
        }
tyClDeclNames _ = []

familyDeclNames :: FamilyDecl GhcRn -> [NameOccurrence]
familyDeclNames FamilyDecl {..} =
  [ NameOccurrence
      { locatedName = L (locA (getLoc fdLName)) (Just (unLoc fdLName))
      , description = "FamilyDecl"
      , isBinder    = True
      }
  ]
familyDeclNames _ = []

familyEqNames :: FamEqn GhcRn (LHsType GhcRn) -> [NameOccurrence]
familyEqNames FamEqn {feqn_tycon = tyCon} =
  [ NameOccurrence
    { locatedName = L (locA (getLoc tyCon)) (Just (unLoc tyCon))
    , description = "FamEqn"
    , isBinder    = False
    }
  ]
familyEqNames _ = []

dataEqNames :: FamEqn GhcRn (HsDataDefn GhcRn) -> [NameOccurrence]
dataEqNames FamEqn {feqn_tycon = tyCon} =
  [ NameOccurrence
      { locatedName = L (locA (getLoc tyCon)) (Just (unLoc tyCon))
      , description = "FamEqn"
      , isBinder    = False
      }
  ]
dataEqNames _ = []

conDeclNames :: ConDecl GhcRn -> [NameOccurrence]
conDeclNames con =
  case con of
    ConDeclGADT {con_names = names} ->
      map
        (\n ->
            NameOccurrence
              { locatedName = L (locA (getLoc n)) (Just (unLoc n))
              , description = "ConDeclGADT"
              , isBinder    = True
              })
        (toList names)
    ConDeclH98 {con_name = name} ->
      [ NameOccurrence
          { locatedName = L (locA (getLoc name)) (Just (unLoc name))
          , description = "ConDeclH98"
          , isBinder    = True
          }
      ]
    _ -> []

foreignDeclNames :: ForeignDecl GhcRn -> [NameOccurrence]
foreignDeclNames decl =
  [ NameOccurrence
      { locatedName = L (locA (getLoc (fd_name decl))) (Just (unLoc (fd_name decl)))
      , description = "ForeignDecl"
      , isBinder    = True
      }
  ]
  
roleAnnotationNames :: RoleAnnotDecl GhcRn -> [NameOccurrence]
roleAnnotationNames (RoleAnnotDecl _ n _) =
  [ NameOccurrence
      { locatedName = L (locA (getLoc n)) (Just (unLoc n))
      , description = "RoleAnnotDecl"
      , isBinder    = False
      }
  ]

injectivityAnnotationNames :: InjectivityAnn GhcRn -> [NameOccurrence]
injectivityAnnotationNames (InjectivityAnn _ lhsName rhsNames) =
  inj lhsName : map inj rhsNames
  where
    inj :: LIdP GhcRn -> NameOccurrence
    inj n =
      NameOccurrence
        { locatedName = L (getLocA n) (Just (unLoc n))
        , description = "InjectivityAnn"
        , isBinder    = False
        }