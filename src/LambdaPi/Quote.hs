module LambdaPi.Quote where

import LambdaPi.Common
import LambdaPi.AST

instance Show Value where
  show = show . quote0

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t)           = Lam (quote (ii + 1) (t (vfree (Quote ii))))
quote ii VStar              = Inf Star
quote ii (VPi v f)          = Inf (Pi (quote ii v)
                                      (quote (ii + 1) (f (vfree (Quote ii)))))
quote ii (VNeutral n)       = Inf (neutralQuote ii n)
quote ii VNat               = Inf Nat
quote ii VZero              = Zero
quote ii (VSucc n)          = Succ (quote ii n)
quote ii (VSigma x f)       = Inf (Sigma (quote ii x) (quote ii f))
quote ii (VComma ty sy x f) = Comma (quote ii ty) (quote ii sy)
                                    (quote ii x) (quote ii f)
quote ii VPoly              = Inf Poly
quote ii (VMkPoly s p)      = MkPoly (quote ii s) (quote ii p)
quote ii (VVec a n)         = Inf (Vec (quote ii a) (quote ii n))
quote ii (VNil a)           = Nil (quote ii a)
quote ii (VCons a n x xs)   = Cons  (quote ii a) (quote ii n)
                                    (quote ii x) (quote ii xs)
quote ii (VEq a x y)        = Inf (Eq (quote ii a) (quote ii x) (quote ii y))
quote ii (VRefl a x)        = Refl (quote ii a) (quote ii x)
quote ii (VFin n)           = Inf (Fin (quote ii n))
quote ii (VFZero n)         = FZero (quote ii n)
quote ii (VFSucc n f)       = FSucc (quote ii n) (quote ii f)
quote ii VBool              = Inf IBool
quote ii VTrue              = CTrue
quote ii VFalse             = CFalse
quote ii (VNamedTy t)       = Inf (NamedTy t)
quote ii (VNamedCon nm t)   = NamedCon nm t

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v)
   =  boundfree ii v
neutralQuote ii (NApp n v)
   =  neutralQuote ii n :$: quote ii v
neutralQuote ii (NNatElim m z s n)
   =  NatElim (quote ii m) (quote ii z) (quote ii s) (Inf (neutralQuote ii n))
neutralQuote ii (NSigElim sy ty motive f arg)
   =  SigElim (quote ii sy) (quote ii ty)
               (quote ii motive) (quote ii f)
               (Inf (neutralQuote ii arg))
neutralQuote ii (NVecElim a m mn mc n xs)
   =  VecElim (quote ii a) (quote ii m)
               (quote ii mn) (quote ii mc)
               (quote ii n) (Inf (neutralQuote ii xs))
neutralQuote ii (NEqElim a m mr x y eq)
   =  EqElim  (quote ii a) (quote ii m) (quote ii mr)
               (quote ii x) (quote ii y)
               (Inf (neutralQuote ii eq))
neutralQuote ii (NFinElim m mz ms n f)
   =  FinElim (quote ii m)
               (quote ii mz) (quote ii ms)
               (quote ii n) (Inf (neutralQuote ii f))
neutralQuote ii (NPolyElim m f val)
   = PolyElim (quote ii m) (quote ii f) (Inf (neutralQuote ii val))
neutralQuote ii (NIf m th el b)
   = If (quote ii m) (quote ii th) (quote ii el) (Inf (neutralQuote ii b))
neutralQuote ii (NEnumElim m val branches)
   = Match (quote ii m) (Inf $ neutralQuote ii val) (fmap (quote ii) branches)

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k)     =  Bound ((ii - k - 1) `max` 0)
boundfree ii x             =  Free x
