module LambdaPi.Eval where

import Common
import LambdaPi.AST
import LambdaPi.Quote
import LambdaPi.Printer
import Debug.Utils

cEval :: Bool -> CTerm -> (NameEnv Value,Env) -> Value
cEval shouldTrace (Inf  ii)        d = traceIf shouldTrace ("eval Inf ") $ iEval shouldTrace ii d
cEval shouldTrace (Lam  c)         d = traceIf shouldTrace "eval lam"
                                     $ VLam (\ x -> cEval shouldTrace c (((\(e, d) -> (e,  (x : d))) d)))
cEval shouldTrace Zero             d = traceIf shouldTrace "eval zero" $ VZero
cEval shouldTrace (Succ k)         d = traceIf shouldTrace "eval zero" $ VSucc (cEval shouldTrace k d)
cEval shouldTrace (Nil a)          d = traceIf shouldTrace "eval Nil" $ VNil (cEval shouldTrace a d)
cEval shouldTrace (Cons a n x xs)  d = traceIf shouldTrace "eval Cons"
                                     $ VCons (cEval shouldTrace a d) (cEval shouldTrace n d)
                                             (cEval shouldTrace x d) (cEval shouldTrace xs d)
cEval shouldTrace (Refl a x)       d = traceIf shouldTrace "eval REFL"
                                     $ VRefl (cEval shouldTrace a d) (cEval shouldTrace x d)
cEval shouldTrace (FZero n)        d = traceIf shouldTrace "eval fin zero" $ VFZero (cEval shouldTrace n d)
cEval shouldTrace (FSucc n f)      d = traceIf shouldTrace "eval fin succ"
                                     $ VFSucc (cEval shouldTrace n d) (cEval shouldTrace f d)
cEval shouldTrace (MkPoly s p)     d = traceIf shouldTrace "eval MkPoly"
                                     $ VMkPoly (cEval shouldTrace s d) (cEval shouldTrace p d)
cEval shouldTrace CTrue            d = traceIf shouldTrace "eval true" $ VTrue
cEval shouldTrace CFalse           d = traceIf shouldTrace "eval false" $ VFalse

iEval :: Bool -> ITerm -> (NameEnv Value,Env) -> Value
iEval shouldTrace (Ann c _)     d = traceIf shouldTrace "eval ann" $  cEval shouldTrace c d
iEval shouldTrace Star          d = traceIf shouldTrace "eval star" $  VStar
iEval shouldTrace (Pi ty ty1)   d = traceIf shouldTrace "eval pi" $  VPi (cEval shouldTrace ty d) (\ x -> cEval shouldTrace ty1 (((\(e, d) -> (e,  (x : d))) d)))
iEval shouldTrace (Bound ii)    d = traceIf shouldTrace "eval bound" $  (snd d) !! ii
iEval shouldTrace (Free x)      d = traceIf shouldTrace "eval free" $  case lookup x (fst d) of Nothing ->  (vfree x); Just v -> v
iEval shouldTrace (i :$: c)     d = traceIf shouldTrace "eval app" $  vapp (iEval shouldTrace i d) (cEval shouldTrace c d)
iEval shouldTrace Nat           d = traceIf shouldTrace "eval net" $  VNat
iEval shouldTrace (NatElim m mz ms n) d
  = traceIf shouldTrace "eval natElim" $
    let  mzVal = cEval shouldTrace mz d
         msVal = cEval shouldTrace ms d
         rec nVal =
           case nVal of
             VZero       ->  mzVal
             VSucc k     ->  (msVal `vapp` k) `vapp` rec k
             VNeutral n  ->  VNeutral
                              (NNatElim (cEval shouldTrace m d) mzVal msVal n)
             _           ->  error "internal: eval natElim"
    in   rec (cEval shouldTrace n d)
iEval shouldTrace (Vec a n)     d = traceIf shouldTrace "eval vec" $ VVec (cEval shouldTrace a d) (cEval shouldTrace n d)
iEval shouldTrace (VecElim a m mn mc n xs) d =
  traceIf shouldTrace "eval vecElim" $
  let  mnVal  =  cEval shouldTrace mn d
       mcVal  =  cEval shouldTrace mc d
       rec nVal xsVal =
         case xsVal of
           VNil _         ->  mnVal
           VCons _ k x xs ->  foldl vapp mcVal [k, x, xs, rec k xs]
           VNeutral n     ->  VNeutral
                                (NVecElim  (cEval shouldTrace a d) (cEval shouldTrace m d)
                                            mnVal mcVal nVal n)
           _              ->  error "internal: eval vecElim"
  in   rec (cEval shouldTrace n d) (cEval shouldTrace xs d)
iEval shouldTrace (Eq a x y)             d  = traceIf shouldTrace "eval eq" $ VEq (cEval shouldTrace a d) (cEval shouldTrace x d) (cEval shouldTrace y d)
iEval shouldTrace (EqElim a m mr x y eq) d  = traceIf shouldTrace "eval eqelim" $ rec (cEval shouldTrace eq d)
  where
     mrVal  =  cEval shouldTrace mr d
     rec eqVal =
       case eqVal of
         VRefl _ z -> mrVal `vapp` z
         VNeutral n ->
           VNeutral (NEqElim  (cEval shouldTrace a d) (cEval shouldTrace m d) mrVal
                                (cEval shouldTrace x d) (cEval shouldTrace y d) n)
         _ -> error "internal: eval eqElim"
iEval shouldTrace (Fin n)                d  = traceIf shouldTrace "eval fin" $ VFin (cEval shouldTrace n d)
iEval shouldTrace (FinElim m mz ms n f)  d  =
  traceIf shouldTrace "eval fin elim" $
  let  mzVal  =  cEval shouldTrace mz d
       msVal  =  cEval shouldTrace ms d
       rec fVal =
         case fVal of
           VFZero k        ->  mzVal `vapp` k
           VFSucc k g      ->  foldl vapp msVal [k, g, rec g]
           VNeutral n'     ->  VNeutral
                                (NFinElim  (cEval shouldTrace m d) (cEval shouldTrace mz d)
                                            (cEval shouldTrace ms d) (cEval shouldTrace n d) n')
           _               ->  error "internal: eval finElim"
  in   rec (cEval shouldTrace f d)
iEval shouldTrace Poly             d = traceIf shouldTrace "eval poly" $ VPoly
iEval shouldTrace (PolyElim m f c) d
  = traceIf shouldTrace "eval polyElim" $
    let fn = cEval shouldTrace f d in case (cEval shouldTrace c d) of
        VMkPoly sh ps -> (fn `vapp` sh) `vapp` ps
        VNeutral n     -> VNeutral (NPolyElim (cEval shouldTrace m d) fn n)
        _ -> error "internal: Eval container"
iEval shouldTrace (Sigma t1 t2) d = traceIf shouldTrace "eval sigma" $ VSigma (cEval shouldTrace t1 d) (cEval shouldTrace t2 d)
iEval shouldTrace (SigElim ty sy motive f arg) d
  = traceIf shouldTrace "eval sigelim" $
    let fn = cEval shouldTrace f d in case (cEval shouldTrace arg d) of
          VComma ty sy a b -> (fn `vapp` a) `vapp` b
          VNeutral n       -> VNeutral (NSigElim (cEval shouldTrace ty d) (cEval shouldTrace sy d) (cEval shouldTrace motive d) fn n)
          _ -> error "internal: Eval container"
iEval shouldTrace IBool  d = traceIf shouldTrace "eval bool" $ VBool
iEval shouldTrace ITrue  d = traceIf shouldTrace "eval true" $ VTrue
iEval shouldTrace IFalse d = traceIf shouldTrace "eval false" $ VFalse
iEval shouldTrace (If m th el bool) d
  = traceIf shouldTrace "eval if" $
    case cEval shouldTrace bool d of
      VTrue -> cEval shouldTrace th d
      VFalse -> cEval shouldTrace el d
      VNeutral n -> VNeutral (NIf (cEval shouldTrace m d) (cEval shouldTrace th d) (cEval shouldTrace el d) n)
      n -> error $ "internal: if on non-bool " ++ show (quote0 n)
