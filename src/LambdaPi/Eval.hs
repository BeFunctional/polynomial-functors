module LambdaPi.Eval where

import Common
import LambdaPi.AST
import LambdaPi.Quote
import Debug.Trace

cEval :: CTerm -> (NameEnv Value,Env) -> Value
cEval (Inf  ii)    d  =  iEval ii d
cEval (Lam  c)     d  =  VLam (\ x -> cEval c (((\(e, d) -> (e,  (x : d))) d)))
cEval Zero      d  = VZero
cEval (Succ k)  d  = VSucc (cEval k d)
cEval (Nil a)          d  =  VNil (cEval a d)
cEval (Cons a n x xs)  d  =  VCons  (cEval a d) (cEval n d)
                                       (cEval x d) (cEval xs d)
cEval (Refl a x)       d  =  VRefl (cEval a d) (cEval x d)
cEval (FZero n)    d  =  VFZero (cEval n d)
cEval (FSucc n f)  d  =  VFSucc (cEval n d) (cEval f d)
cEval (MkPoly s p) d  =  VMkPoly (cEval s d) (cEval p d)
cEval CTrue         d  = VTrue
cEval CFalse        d  = VFalse

iEval :: ITerm -> (NameEnv Value,Env) -> Value
iEval (Ann c _)     d  =  cEval c d
iEval Star          d  =  VStar
iEval (Pi ty ty1)   d  =  VPi (cEval ty d) (\ x -> cEval ty1 (((\(e, d) -> (e,  (x : d))) d)))
iEval (Free x)      d  =  case lookup x (fst d) of Nothing ->  (vfree x); Just v -> v
iEval (Bound ii)    d  =  (snd d) !! ii
iEval (i :$: c)     d  =  vapp (iEval i d) (cEval c d)
iEval Nat           d  =  VNat
iEval (NatElim m mz ms n) d
  =  let  mzVal = cEval mz d
          msVal = cEval ms d
          rec nVal =
            case nVal of
              VZero       ->  mzVal
              VSucc k     ->  (msVal `vapp` k) `vapp` rec k
              VNeutral n  ->  VNeutral
                               (NNatElim (cEval m d) mzVal msVal n)
              _           ->  error "internal: eval natElim"
     in   rec (cEval n d)
iEval Poly          d  =  VPoly
iEval (PolyElim m f c) d
  = let fn = cEval f d in case (cEval c d) of
        VMkPoly sh ps -> (fn `vapp` sh) `vapp` ps
        VNeutral n     -> VNeutral (NPolyElim (cEval m d) fn n)
        _ -> error "internal: Eval container"

iEval (Vec a n)     d  =  VVec (cEval a d) (cEval n d)
iEval (VecElim a m mn mc n xs) d =
  let  mnVal  =  cEval mn d
       mcVal  =  cEval mc d
       rec nVal xsVal =
         case xsVal of
           VNil _         ->  mnVal
           VCons _ k x xs ->  foldl vapp mcVal [k, x, xs, rec k xs]
           VNeutral n     ->  VNeutral
                                (NVecElim  (cEval a d) (cEval m d)
                                            mnVal mcVal nVal n)
           _              ->  error "internal: eval vecElim"
  in   rec (cEval n d) (cEval xs d)
iEval (Eq a x y)             d  =  VEq (cEval a d) (cEval x d) (cEval y d)
iEval (EqElim a m mr x y eq) d  = rec (cEval eq d)
  where
     mrVal  =  cEval mr d
     rec eqVal =
       case eqVal of
         VRefl _ z -> mrVal `vapp` z
         VNeutral n ->
           VNeutral (NEqElim  (cEval a d) (cEval m d) mrVal
                                (cEval x d) (cEval y d) n)
         _ -> error "internal: eval eqElim"
iEval (Fin n)                d  =  VFin (cEval n d)
iEval (FinElim m mz ms n f)  d  =
  let  mzVal  =  cEval mz d
       msVal  =  cEval ms d
       rec fVal =
         case fVal of
           VFZero k        ->  mzVal `vapp` k
           VFSucc k g      ->  foldl vapp msVal [k, g, rec g]
           VNeutral n'     ->  VNeutral
                                (NFinElim  (cEval m d) (cEval mz d)
                                            (cEval ms d) (cEval n d) n')
           _               ->  error "internal: eval finElim"
  in   rec (cEval f d)
iEval IBool d = VBool
iEval (If m th el bool) d =
  case cEval bool d of
    VTrue -> cEval th d
    VFalse -> cEval el d
    VNeutral n -> VNeutral (NIf (cEval m d) (cEval th d) (cEval el d) n)
    n -> error $ "internal: if on non-bool " ++ show (quote0 n)
iEval (SigElim ty sy motive f arg) d =
  let fn = cEval f d in case (cEval arg d) of
        VComma ty sy a b -> trace "found constructor" $ (fn `vapp` a) `vapp` b
        VNeutral n       -> trace "found neutral term" $ VNeutral (NSigElim (cEval ty d) (cEval sy d) (cEval motive d) fn n)
        _ -> error "internal: Eval container"
