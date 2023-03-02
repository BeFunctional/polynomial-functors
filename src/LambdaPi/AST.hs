module LambdaPi.AST where

import LambdaPi.Common

import Data.Text

data CTerm
   =  Inf  ITerm
   |  Lam  CTerm
   |  Zero
   |  Succ CTerm
   |  Nil CTerm
   |  Cons CTerm CTerm CTerm CTerm
   |  Refl CTerm CTerm
   |  FZero CTerm       -- Fin zero
   |  FSucc CTerm CTerm -- Fin succ
   |  MkPoly CTerm CTerm            -- constructor poly
   |  Comma CTerm CTerm CTerm CTerm -- constructor for Sigma
   |  CTrue
   |  CFalse
   |  NamedCon Text Int -- named constructor, user defined, int is tag
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Star
   |  NamedTy Text -- named type, user defined
   -- eliminator for user-defined type
   |  Match {- motive    -} CTerm
            {- scrutinee -} CTerm
            {- patterns  -} [(Text, CTerm)]  -- List of patterns and RHS
   |  Pi CTerm CTerm
   |  Bound  Int
   |  Free  Name
   |  ITerm :$: CTerm
   |  Nat
   |  NatElim CTerm CTerm CTerm CTerm
   |  Vec CTerm CTerm
   |  VecElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Eq CTerm CTerm CTerm
   |  EqElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Fin CTerm -- Fin type
   |  FinElim CTerm CTerm CTerm CTerm CTerm
   |  Poly -- type poly
   |  PolyElim CTerm CTerm CTerm -- Eliminator for Poly
   |  Sigma CTerm CTerm -- Type of Σ
   |  SigElim CTerm CTerm CTerm CTerm CTerm -- Eliminator for Sigma
   |  IBool
   |  ITrue
   |  IFalse
   |  If CTerm CTerm CTerm CTerm -- dependent if
  deriving (Show, Eq)

data Value
   =  VLam  (Value -> Value)
   |  VStar
   |  VPi Value (Value -> Value)
   |  VNeutral Neutral
   |  VNat
   |  VZero
   |  VSucc Value
   |  VNil Value
   |  VCons Value Value Value Value
   |  VVec Value Value
   |  VEq Value Value Value
   |  VRefl Value Value
   |  VFZero Value
   |  VFSucc Value Value
   |  VFin Value -- Fin Type
   |  VPoly -- Type Poly
   |  VMkPoly Value Value -- Constructor for poly
   |  VSigma Value Value -- Type Sigma
   |  VComma Value Value Value Value -- Consturctor for Sigma
   |  VBool
   |  VTrue
   |  VFalse
   |  VNamedCon Text Int
   |  VNamedTy Text

data Neutral
   =  NFree Name
   |  NApp Neutral Value
   |  NNatElim Value Value Value Neutral
   |  NVecElim Value Value Value Value Value Neutral
   |  NEqElim Value Value Value Value Value Neutral
   |  NFinElim Value Value Value Value Neutral
   |  NPolyElim Value Value Neutral
   |  NSigElim Value Value Value Value Neutral

   |  NIf {- motive    -} Value
          {- ifTrue    -} Value
          {- ifFalse   -} Value
          {- scrutinee -} Neutral

   |  NEnumElim {- motive    -} Value
                {- scrutinee -} Neutral
                {- branches  -} [(Text, Value)]

type Env = [Value]
type Type = Value
type Context = [(Name, Type)]


vapp :: Value -> Value -> Value
vapp (VLam f)      v  =  f v
vapp (VNeutral n)  v  =  VNeutral (NApp n v)
vapp n v = error $ "tried to apply to something that is not a lambda nor a neutral term"


vfree :: Name -> Value
vfree n = VNeutral (NFree n)
