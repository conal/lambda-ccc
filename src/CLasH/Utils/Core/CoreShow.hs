{-# LANGUAGE StandaloneDeriving,FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
--
-- This module derives Show instances for CoreSyn types.
--
module CLasH.Utils.Core.CoreShow where

-- From CLasH, with lots of hacks/tweaks for GHC 7.6 by Conal Elliott

-- GHC API
import qualified BasicTypes
import qualified CoreSyn
import qualified TypeRep
import qualified TyCon
import qualified HsTypes
import qualified HsExpr
import qualified HsBinds
import qualified SrcLoc
import qualified RdrName
import qualified Module
import qualified Coercion
import qualified Literal
import qualified NameSet
import qualified Var
import qualified Name
import qualified TcEvidence
import qualified HsPat
import qualified DataCon
import qualified HsLit
import qualified HsDecls
import qualified InstEnv
import qualified Class
import qualified ForeignCall
import qualified Bag
import qualified GHC.IORef
import qualified VarSet

import qualified Language.HERMIT.GHC as HG

import Outputable ( Outputable, OutputableBndr, showSDoc, ppr)

-- Fill-ins:
instance Show (CoreSyn.Tickish b) where show _ = "<Tickish>"
instance Show Coercion.Coercion where show _ = "<Coercion>"
instance Show CoreSyn.AltCon where show _ = "<AltCon>"
instance Show Literal.Literal where show _ = "<Literal>"
instance Show NameSet.FreeVars where show _ = "<FreeVars>"
instance Show Name.Name where show _ = "<Name>"
instance Show DataCon.DataCon where show _ = "<DataCon>"
instance Show (HsBinds.LHsBindsLR n n) where show _ = "<LHsBindsLR>"
instance Show Class.Class where show _ = "<Class>"
instance Show (Bag.Bag z) where show _ = "<Bag>"
instance Show (GHC.IORef.IORef a) where show _ = "<IORef>"
instance Show Module.Module where show _ = "<Module>"
instance Show Module.ModuleName where show _ = "<ModuleName>"
instance Show Name.OccName where show _ = "<OccName>"
instance Show VarSet.TyVarSet where show _ = "<TyVarSet>"
instance Show Module.PackageId where show _ = "<PackageId>"

-- instance Show Var.Id where show _ = "<Id>"
instance Show Var.Id where show = HG.fqName . Var.varName

-- Derive Show for core expressions and binders, so we can see the actual
-- structure.
deriving instance Show HsTypes.HsTyLit
deriving instance Show HsTypes.HsBang
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.HsType n)
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.HsTyVarBndr n)
deriving instance (Show b) => Show (CoreSyn.Expr b)
deriving instance (Show b) => Show (CoreSyn.Bind b)
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.HsSplice n)
deriving instance Show n => Show (HsTypes.HsQuasiQuote n)
deriving instance Show HsTypes.HsIPName
deriving instance Show HsTypes.HsTyWrapper
deriving instance Show HsTypes.HsTupleSort
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.LHsTyVarBndrs n)
deriving instance Show HsTypes.HsExplicitFlag
deriving instance Show TcEvidence.HsWrapper
deriving instance Show TcEvidence.EvTerm
deriving instance Show TcEvidence.EvLit
deriving instance Show TcEvidence.TcCoercion
deriving instance Show TcEvidence.EvBindsVar
deriving instance Show TypeRep.TyLit
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.HsExpr n)
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.HsCmdTop n)
deriving instance (Show n, OutputableBndr n) => Show (HsPat.Pat n)
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.HsBracket n)
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.ArithSeqInfo n)
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.HsRecordBinds n)
deriving instance Show TypeRep.Type
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.StmtLR n n)
deriving instance (Show n, OutputableBndr n) => Show (HsBinds.HsLocalBinds n)
deriving instance Show BasicTypes.Fixity
deriving instance Show BasicTypes.InlinePragma
deriving instance Show BasicTypes.RecFlag
deriving instance Show BasicTypes.Activation
deriving instance Show BasicTypes.WarningTxt
deriving instance Show BasicTypes.FixityDirection
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.GRHS n)
deriving instance Show HsLit.HsLit
deriving instance (Show n, OutputableBndr n) => Show (HsLit.HsOverLit n)
deriving instance Show t => Show (HsTypes.HsWithBndrs t)
deriving instance Show TcEvidence.TcEvBinds
deriving instance (Show n, OutputableBndr n) => Show (HsPat.HsConPatDetails n)
deriving instance (Show n, Show e) => Show (HsPat.HsRecField n e)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.HsDecl n)
deriving instance (Show n, OutputableBndr n) =>Show (HsDecls.HsGroup n)
deriving instance Show HsExpr.TransForm
deriving instance (Show n, OutputableBndr n) => Show (HsExpr.ParStmtBlock n n)
deriving instance (Show n, OutputableBndr n) => Show (HsBinds.HsIPBinds n)
deriving instance Show n => Show (HsBinds.ABExport n)
deriving instance Show HsBinds.TcSpecPrags
deriving instance Show HsBinds.TcSpecPrag
deriving instance Show n => Show (HsBinds.FixitySig n)
deriving instance (Show n, OutputableBndr n) => Show (HsBinds.Sig n)
deriving instance (Show n, OutputableBndr n) => Show (HsBinds.IPBind n)
deriving instance (Show n, OutputableBndr n) => Show (HsBinds.HsValBindsLR n n)
deriving instance Show HsLit.OverLitVal
deriving instance (Show n, Show l) => Show (HsPat.HsRecFields n l)
deriving instance Show HsDecls.DocDecl
-- deriving instance (Show n, OutputableBndr n) => Show (HsTypes.HsType n)
deriving instance (Show n, OutputableBndr n) => Show (HsTypes.ConDeclField n)
deriving instance (Show x) => Show (SrcLoc.Located x)
-- deriving instance (Show x, OutputableBndr x) => Show (HsExpr.StmtLR x x)
deriving instance (Show x, OutputableBndr x) => Show (HsExpr.HsTupArg x)
-- deriving instance (Show x, OutputableBndr x) => Show (HsExpr.HsExpr x)
deriving instance Show (RdrName.RdrName)
deriving instance (Show (HsBinds.ABExport idL), Show idL, Show idR, OutputableBndr idL, OutputableBndr idR) => Show (HsBinds.HsBindLR idL idR)
-- deriving instance Show CoreSyn.Note
deriving instance Show TyCon.SynTyConRhs
deriving instance Show TyCon.CoAxiom
deriving instance Show HsDecls.ForeignExport
deriving instance Show HsDecls.ForeignImport
deriving instance Show HsDecls.FamilyFlavour
deriving instance Show HsDecls.NewOrData
deriving instance Show HsDecls.CImportSpec
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.SpliceDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.VectDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.RuleDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.RuleBndr n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.AnnDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.WarnDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.ForeignDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.DefaultDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.DerivDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.InstDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.TyClDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.ConDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.HsTyDefn n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.AnnProvenance n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.FamInstDecl n)
deriving instance (Show n, OutputableBndr n) => Show (HsDecls.HsConDeclDetails n)
deriving instance Show l => Show (HsDecls.ResType l)
deriving instance Show InstEnv.ClsInst
deriving instance Show InstEnv.OverlapFlag
deriving instance Show ForeignCall.CType
deriving instance Show ForeignCall.CExportSpec
deriving instance Show ForeignCall.CCallTarget
deriving instance Show ForeignCall.CCallConv
deriving instance Show ForeignCall.Header

-- Implement dummy shows, since deriving them will need loads of other shows
-- as well.
-- instance Show TypeRep.PredType where
--   show t = "_PredType:(" ++ showSDoc (ppr t) ++ ")"
instance Show TyCon.TyCon where
  show t | TyCon.isAlgTyCon t && not (TyCon.isTupleTyCon t) =
           showtc "AlgTyCon" ""
--          | TyCon.isCoercionTyCon t =
--            showtc "CoercionTyCon" ""
         | TyCon.isSynTyCon t =
           showtc "SynTyCon" (", synTcRhs = " ++ synrhs)
         | TyCon.isTupleTyCon t =
           showtc "TupleTyCon" ""
         | TyCon.isFunTyCon t =
           showtc "FunTyCon" ""
         | TyCon.isPrimTyCon t =
           showtc "PrimTyCon" ""
--          | TyCon.isSuperKindTyCon t =
--            showtc "SuperKindTyCon" ""
         | otherwise = 
           "_Nonexistant tycon?:(" ++ "..." {-showSDoc (ppr t)-} ++ ")_"
      where
        showtc con extra = "(" ++ con ++ " {tyConName = " ++ name ++ extra ++ ", ...})"
        name = show (TyCon.tyConName t)
        synrhs = show (TyCon.synTyConRhs t)
instance Show BasicTypes.Boxity where
  show b = "_Boxity"
-- instance Show HsTypes.HsExplicitForAll where
--   show b = "_HsExplicitForAll"
instance Show HsExpr.HsArrAppType where
  show b = "_HsArrAppType"
instance Show (HsExpr.MatchGroup x) where
  show b = "_HsMatchGroup"
-- instance Show (HsExpr.GroupByClause x) where
--   show b = "_GroupByClause"
instance Show (HsExpr.HsStmtContext x) where
  show b = "_HsStmtContext"
-- instance Show (HsBinds.Prag) where
--   show b = "_Prag"
instance Show (HsExpr.GRHSs id) where
  show b = "_GRHSs"


-- instance (Outputable x) => Show x where
--   show x = "__" ++ showSDoc (ppr x) ++ "__"
