module LambdaPi.Eval where

import LambdaPi.Common
import LambdaPi.AST
import LambdaPi.Quote
import LambdaPi.Printer

import Data.Bifunctor (second)
import Data.Maybe (fromJust)
import Debug.Utils

cEval :: Bool -> (NameEnv Value, Env) -> CTerm ->  Value
cEval shouldTrace d (Inf  ii)           = traceIf shouldTrace ("eval Inf ") $ iEval shouldTrace d ii
cEval shouldTrace d (Lam  c)            = traceIf shouldTrace "eval lam"
                                        $ VLam (\x -> cEval shouldTrace ((\(e, d) -> (e,  (x : d))) d)c )
cEval shouldTrace d Zero                = traceIf shouldTrace "eval zero" $ VZero
cEval shouldTrace d (Succ k)            = traceIf shouldTrace "eval zero"
                                        $ VSucc (cEval shouldTrace d k)
cEval shouldTrace d (Nil a)             = traceIf shouldTrace "eval Nil"
                                        $ VNil (cEval shouldTrace d a)
cEval shouldTrace d (Cons a n x xs)     = traceIf shouldTrace "eval Cons"
                                        $ VCons (cEval shouldTrace d a)
                                                (cEval shouldTrace d n)
                                                (cEval shouldTrace d x)
                                                (cEval shouldTrace d xs)
cEval shouldTrace d (Refl a x)          = traceIf shouldTrace "eval REFL"
                                        $ VRefl (cEval shouldTrace d a)
                                                (cEval shouldTrace d x)
cEval shouldTrace d (FZero n)           = traceIf shouldTrace "eval fin zero"
                                        $ VFZero (cEval shouldTrace d n)
cEval shouldTrace d (FSucc n f)         = traceIf shouldTrace "eval fin succ"
                                        $ VFSucc (cEval shouldTrace d n)
                                                 (cEval shouldTrace d f)
cEval shouldTrace d (MkPoly s p)        = traceIf shouldTrace "eval MkPoly"
                                        $ VMkPoly (cEval shouldTrace d s)
                                                  (cEval shouldTrace d p)
cEval shouldTrace d (Comma t1 t2 v1 v2) = traceIf shouldTrace "eval comma"
                                        $ VComma (cEval shouldTrace d t1)
                                                 (cEval shouldTrace d t2)
                                                 (cEval shouldTrace d v1)
                                                 (cEval shouldTrace d v2)
cEval shouldTrace d (NamedCon nm t)     = traceIf shouldTrace "eval named constructor"
                                        $ VNamedCon nm t

iEval :: Bool -> (NameEnv Value,Env) -> ITerm -> Value
iEval shouldTrace d (Ann c _)     = traceIf shouldTrace "eval ann" $  cEval shouldTrace d c
iEval shouldTrace d Star          = traceIf shouldTrace "eval star" $  VStar
iEval shouldTrace d (Pi ty ty1)   = traceIf shouldTrace "eval pi"
                                  $ VPi (cEval shouldTrace d ty)
                                        (\x -> cEval shouldTrace ((\(e, d) -> (e,  (x : d))) d) ty1)
iEval shouldTrace d (Bound ii)    = traceIf shouldTrace "eval bound" $  (snd d) !! ii
iEval shouldTrace d (Free x)      = traceIf shouldTrace "eval free"
                                  $ case lookup x (fst d) of
                                         Nothing -> traceIf shouldTrace (show x ++ " not found, free variable") (vfree x)
                                         Just v -> traceIf shouldTrace ("found " ++ show x) v
iEval shouldTrace d (i :$: c)     = traceIf shouldTrace "eval app"
                                  $ vapp (iEval shouldTrace d i) (cEval shouldTrace d c)
iEval shouldTrace d Nat           = traceIf shouldTrace "eval net" $ VNat
iEval shouldTrace d (NatElim m mz ms n)
  = traceIf shouldTrace "eval natElim"
  $ let  mzVal = cEval shouldTrace d mz
         msVal = cEval shouldTrace d ms
         rec nVal =
           case nVal of
             VZero       ->  mzVal
             VSucc k     ->  (msVal `vapp` k) `vapp` rec k
             VNeutral n  ->  VNeutral
                              (NNatElim (cEval shouldTrace d m) mzVal msVal n)
             _           ->  error "internal: eval natElim"
    in   rec (cEval shouldTrace d n)
iEval shouldTrace d (Vec a n)     = traceIf shouldTrace "eval vec" $ VVec (cEval shouldTrace d a) (cEval shouldTrace d n)
iEval shouldTrace d (VecElim a m mn mc n xs) =
  traceIf shouldTrace "eval vecElim" $
  let  mnVal  =  cEval shouldTrace d mn
       mcVal  =  cEval shouldTrace d mc
       rec nVal xsVal =
         case xsVal of
           VNil _         ->  mnVal
           VCons _ k x xs ->  foldl vapp mcVal [k, x, xs, rec k xs]
           VNeutral n     ->  VNeutral
                                (NVecElim  (cEval shouldTrace d a) (cEval shouldTrace d m)
                                            mnVal mcVal nVal n)
           _              ->  error "internal: eval vecElim"
  in   rec (cEval shouldTrace d n) (cEval shouldTrace d xs)
iEval shouldTrace d (Eq a x y)
  = traceIf shouldTrace "eval eq"
  $ VEq (cEval shouldTrace d a) (cEval shouldTrace d x) (cEval shouldTrace d y)
iEval shouldTrace d (EqElim a m mr x y eq)
  = traceIf shouldTrace "eval eqelim" $ rec (cEval shouldTrace d eq)
  where
     mrVal  =  cEval shouldTrace d mr
     rec eqVal =
       case eqVal of
         VRefl _ z -> mrVal `vapp` z
         VNeutral n ->
           VNeutral (NEqElim  (cEval shouldTrace d a) (cEval shouldTrace d m) mrVal
                                (cEval shouldTrace d x) (cEval shouldTrace d y) n)
         _ -> error "internal: eval eqElim"
iEval shouldTrace d (Fin n)                = traceIf shouldTrace "eval fin" $ VFin (cEval shouldTrace d n)
iEval shouldTrace d (FinElim m mz ms n f)  =
  traceIf shouldTrace "eval fin elim" $
  let  mzVal  =  cEval shouldTrace d mz
       msVal  =  cEval shouldTrace d ms
       rec fVal =
         case fVal of
           VFZero k        ->  mzVal `vapp` k
           VFSucc k g      ->  foldl vapp msVal [k, g, rec g]
           VNeutral n'     ->  VNeutral
                                (NFinElim  (cEval shouldTrace d m) (cEval shouldTrace d mz)
                                            (cEval shouldTrace d ms) (cEval shouldTrace d n) n')
           _               ->  error "internal: eval finElim"
  in   rec (cEval shouldTrace d f)
iEval shouldTrace d Poly             = traceIf shouldTrace "eval poly" $ VPoly
iEval shouldTrace d (PolyElim m f c)
  = traceIf shouldTrace "eval polyElim" $
    let fn = cEval shouldTrace d f in case (cEval shouldTrace d c) of
        VMkPoly sh ps -> (fn `vapp` sh) `vapp` ps
        VNeutral n     -> VNeutral (NPolyElim (cEval shouldTrace d m) fn n)
        _ -> error "internal: Eval container"
iEval shouldTrace d (Sigma t1 t2) = traceIf shouldTrace "eval sigma" $ VSigma (cEval shouldTrace d t1) (cEval shouldTrace d t2)
iEval shouldTrace d (SigElim ty sy motive f arg)
  = traceIf shouldTrace "eval sigelim" $
    let fn = cEval shouldTrace d f in case (cEval shouldTrace d arg) of
          VComma ty sy a b -> (fn `vapp` a) `vapp` b
          VNeutral n       -> VNeutral (NSigElim (cEval shouldTrace d ty) (cEval shouldTrace d sy) (cEval shouldTrace d motive) fn n)
          _ -> error "internal: Eval container"
iEval shouldTrace d (NamedTy nm) = traceIf shouldTrace "eval namedTy" $ VNamedTy nm
iEval shouldTrace d (Match m scrutinee branches) = traceIf shouldTrace "eval Match"
  $ case cEval shouldTrace d scrutinee of
      VNamedCon nm tag -> cEval shouldTrace d (fromJust $ lookup nm branches)
      VNeutral n -> VNeutral $
          NEnumElim (cEval shouldTrace d m) n (fmap (second (\x -> cEval shouldTrace d x)) branches)
      n -> error $ "internal: matching on incorrect type " ++ show (quote0 n)
