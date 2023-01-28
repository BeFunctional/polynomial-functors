module LambdaPi.Check where

import Text.PrettyPrint.HughesPJ hiding (parens, (<>), render)

import Control.Monad.Except (throwError, unless)

import Data.Text (Text)
import Common
import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Quote
import LambdaPi.Printer

import Debug.Utils

iType0 :: Bool -> (NameEnv Value,Context) -> ITerm -> Result Type
iType0 shouldTrace = iType shouldTrace 0

iType :: Bool -> Int -> (NameEnv Value,Context) -> ITerm -> Result Type
iType shouldTrace ii g (Ann e tyt)
  = traceIf shouldTrace "iType Ann" $
    do cType shouldTrace  ii g tyt VStar
       let ty = cEval shouldTrace tyt (fst g, [])
       cType shouldTrace ii g e ty
       return ty
iType shouldTrace ii g Star
   = traceIf shouldTrace "iType Star" $ return VStar
iType shouldTrace ii g (Pi tyt tyt')
   = traceIf shouldTrace "iType Pi" $
     do cType shouldTrace ii g tyt VStar
        let ty = cEval shouldTrace tyt (fst g, [])
        cType shouldTrace  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)
                  (cSubst 0 (Free (Local ii)) tyt') VStar
        return VStar
iType shouldTrace ii g (Free x)
  = traceIf shouldTrace ("iType free: '" <> show x <> "'") $
        case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  throwError ("unknown identifier: " <> render (iPrint 0 0 (Free x)))
iType shouldTrace ii g (e1 :$: e2)
  = traceIf shouldTrace ("iType app '" <> show (iPrint 0 0 e1) <> "' applied to '" <> show (cPrint 0 0 e2) <> "'") $
        do  si <- iType shouldTrace ii g e1
            case si of
              VPi  ty ty1 -> do cType shouldTrace ii g e2 ty
                                return ( ty1 (cEval shouldTrace e2 (fst g, [])))
              _           -> throwError $ "illegal application : " <> tshow e2 <> "applyed to " <> tshow e1
iType shouldTrace ii g Nat                  = traceIf shouldTrace "iType Nat" $ return VStar
iType shouldTrace ii g (NatElim m mz ms n)
  = traceIf shouldTrace "iType NatElim" $
  do  cType shouldTrace ii g m (VPi VNat (const VStar))
      let mVal  = cEval shouldTrace m (fst g, [])
      cType shouldTrace ii g mz (mVal `vapp` VZero)
      cType shouldTrace ii g ms (VPi VNat (\k -> VPi (mVal `vapp` k) (\_ -> mVal `vapp` VSucc k)))
      cType shouldTrace ii g n VNat
      let nVal = cEval shouldTrace n (fst g, [])
      return (mVal `vapp` nVal)

iType shouldTrace ii g (Sigma f s)
  = traceIf shouldTrace "iType Sigma" $ do
    cType shouldTrace ii g f VStar
    let fVal = cEval shouldTrace f (fst g, [])
    cType shouldTrace ii g s (VPi fVal (const VStar))
    return VStar
iType shouldTrace ii g (SigElim ty fty m f p)
  = traceIf shouldTrace "iType SigElim" $ do
    cType shouldTrace ii g ty VStar
    let tyVal = cEval shouldTrace ty (fst g, [])
    sig <- cType shouldTrace ii g fty (VPi tyVal (const VStar))
    let fyVal = cEval shouldTrace fty (fst g, [])
    -- m : Sigma ty fy -> Type
    cType shouldTrace ii g m (VPi (VSigma tyVal fyVal) (const VStar))
    let mVal = cEval shouldTrace m (fst g, [])
    cType shouldTrace ii g f (VPi (VSigma tyVal fyVal) (\sig -> mVal `vapp` sig))
    cType shouldTrace ii g p (VSigma tyVal fyVal)
    let product = cEval shouldTrace p (fst g, [])
    return $ mVal `vapp` product

iType shouldTrace ii g Poly             = traceIf shouldTrace "iType poly" $ return VStar -- Poly is a type
iType shouldTrace ii g (PolyElim m f c)
  = traceIf shouldTrace "iType polyElim" $ do
    cType shouldTrace ii g m (VPi VPoly (\_ -> VStar)) -- check the motive
    let mVal = cEval shouldTrace m (fst g, []) -- quote the motive
    cType shouldTrace ii g c VPoly -- check the argument
    -- check the elimination function whose type depends on both arguments
    cType shouldTrace ii g f (VPi VStar (\shapes ->
                   VPi (VPi shapes (const VStar)) (\positions ->
                   mVal `vapp` VMkPoly shapes positions)))
    let cVal = cEval shouldTrace c (fst g, []) -- quote the container
    return (mVal `vapp` cVal)

iType shouldTrace ii g (Vec a n)
  = traceIf shouldTrace "iType vec" $ do
    cType shouldTrace ii g a  VStar
    cType shouldTrace ii g n  VNat
    return VStar
iType shouldTrace ii g (VecElim a m mn mc n vs)
  = traceIf shouldTrace "iType VecElim" $ do
    cType shouldTrace ii g a VStar
    let aVal = cEval shouldTrace a (fst g, [])
    cType shouldTrace ii g m
      ( VPi VNat (\n -> VPi (VVec aVal n) (\_ -> VStar)))
    let mVal = cEval shouldTrace m (fst g, [])
    cType shouldTrace ii g mn (foldl vapp mVal [VZero, VNil aVal])
    cType shouldTrace ii g mc
      (  VPi VNat (\ n ->
         VPi aVal (\ y ->
         VPi (VVec aVal n) (\ ys ->
         VPi (foldl vapp mVal [n, ys]) (\_ ->
         (foldl vapp mVal [VSucc n, VCons aVal n y ys]))))))
    cType shouldTrace ii g n VNat
    let nVal = cEval shouldTrace n (fst g, [])
    cType shouldTrace ii g vs (VVec aVal nVal)
    let vsVal = cEval shouldTrace vs (fst g, [])
    return (foldl vapp mVal [nVal, vsVal])
iType shouldTrace i g (Eq a x y)
  = traceIf shouldTrace "iType Eq" $ do
    cType shouldTrace i g a VStar
    let aVal = cEval shouldTrace a (fst g, [])
    cType shouldTrace i g x aVal
    cType shouldTrace i g y aVal
    return VStar
iType shouldTrace i g (EqElim a m mr x y eq)
  = traceIf shouldTrace "iType EqElim" $ do
    cType shouldTrace i g a VStar
    let aVal = cEval shouldTrace a (fst g, [])
    cType shouldTrace i g m
      (VPi aVal (\ x ->
       VPi aVal (\ y ->
       VPi (VEq aVal x y) (\_ -> VStar))))
    let mVal = cEval shouldTrace m (fst g, [])
    cType shouldTrace i g mr
      (VPi aVal (\ x ->
       foldl vapp mVal [x, x, VRefl aVal x]))
    cType shouldTrace i g x aVal
    let xVal = cEval shouldTrace x (fst g, [])
    cType shouldTrace i g y aVal
    let yVal = cEval shouldTrace y (fst g, [])
    cType shouldTrace i g eq (VEq aVal xVal yVal)
    let eqVal = cEval shouldTrace eq (fst g, [])
    return (foldl vapp mVal [xVal, yVal, eqVal])
iType shouldTrace ii g (Fin n)
  = traceIf shouldTrace "iType fin" $ do
    cType shouldTrace ii g n VNat
    return VStar
iType shouldTrace ii g (FinElim m mz ms n f)
  = traceIf shouldTrace "iType FinElim" $ do
    cType shouldTrace ii g m (VPi VNat (\k -> VPi (VFin k) (const VStar)))
    let mVal  = cEval shouldTrace m (fst g, [])
    cType shouldTrace ii g n VNat
    let nVal = cEval shouldTrace n (fst g, [])
    cType shouldTrace ii g mz (VPi VNat (\k -> mVal `vapp` VSucc k `vapp` VFZero k))
    cType shouldTrace ii g ms (VPi VNat (\k ->
        VPi (VFin k) (\fk ->
            VPi (mVal `vapp` k `vapp` fk) (\_ ->
                mVal `vapp` VSucc k `vapp` VFSucc k fk))))
    cType shouldTrace ii g f (VFin nVal)
    let fVal = cEval shouldTrace f (fst g, [])
    return (mVal `vapp` nVal `vapp` fVal)
iType shouldTrace _ _ tm = throwError $ "No type match for " <> render (iPrint 0 0 tm)

cType :: Bool -> Int -> (NameEnv Value,Context) -> CTerm -> Type -> Result ()
cType shouldTrace ii g (Inf e) v
  = traceIf shouldTrace "cType Inf" $ do
    v' <- iType shouldTrace ii g e
    unless ( quote0 v == quote0 v')
           (throwError ("type mismatch:\n"
                     <> "type inferred:  "
                     <> render (cPrint 0 0 (quote0 v')) <> "\n"
                     <> "type expected:  " <> render (cPrint 0 0 (quote0 v)) <> "\n"
                     <> "for expression: " <> render (iPrint 0 0 e)))
cType shouldTrace ii g (Lam e) ( VPi ty ty')
  = traceIf shouldTrace ("cType PI " <> show (cPrint 0 0 (quote 0 ty)) ) $
    cType shouldTrace  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty ) : g))) g)
           (cSubst 0 (Free (Local ii)) e) ( ty' (vfree (Local ii)))
cType shouldTrace ii g Zero      VNat  = traceIf shouldTrace "cType Zero" $ return ()
cType shouldTrace ii g (Succ k)  VNat  = traceIf shouldTrace "cType Succ" $ cType shouldTrace ii g k VNat
cType shouldTrace ii g (Comma ty sy x f) (VSigma ty' fy')
  = traceIf shouldTrace "cType Comma" $ do
    cType shouldTrace ii g x ty'
    let xVal = cEval shouldTrace x (fst g, [])
    unless (quote0 xVal == quote0 ty')
           (throwError $ "type mismatch:\n"
                      <> "given: " <> render (cPrint 0 0 (quote0 xVal)) <> "\n"
                      <> "expected: " <> render (cPrint 0 0 (quote0 ty')) <> "\n")
    cType shouldTrace ii g f fy'

cType shouldTrace ii g (MkPoly x f) VPoly
  = traceIf shouldTrace "cType MkPoly" $ do
    cType shouldTrace ii g x VStar -- check if the first argument is a type
    let xVal = cEval shouldTrace x (fst g, [])
    cType shouldTrace ii g f (VPi xVal (const VStar)) -- check if the second argument is a Π
cType shouldTrace ii g (Nil a) (VVec bVal VZero)
  = traceIf shouldTrace "cType Nil" $ do
    cType shouldTrace ii g a VStar
    let aVal = cEval shouldTrace a (fst g, [])
    unless  (quote0 aVal == quote0 bVal)
            (throwError "type mismatch")
cType shouldTrace ii g (Cons a n x xs) (VVec bVal (VSucc k))
  = traceIf shouldTrace "cType Cons" $ do
    cType shouldTrace ii g a VStar
    let aVal = cEval shouldTrace a (fst g, [])
    unless  (quote0 aVal == quote0 bVal)
            (throwError "type mismatch")
    cType shouldTrace ii g n VNat
    let nVal = cEval shouldTrace n (fst g, [])
    unless  (quote0 nVal == quote0 k)
            (throwError "number mismatch")
    cType shouldTrace ii g x aVal
    cType shouldTrace ii g xs (VVec bVal k)
cType shouldTrace ii g (Refl a z) (VEq bVal xVal yVal)
  = traceIf shouldTrace "cType REFL" $ do
    cType shouldTrace ii g a VStar
    let aVal = cEval shouldTrace a (fst g, [])
    unless  (quote0 aVal == quote0 bVal)
            (throwError "type mismatch")
    cType shouldTrace ii g z aVal
    let zVal = cEval shouldTrace z (fst g, [])
    unless  (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
            (throwError "type mismatch")
cType shouldTrace ii g@(v,t) (FZero n) (VFin (VSucc mVal))
  = traceIf shouldTrace "cType fin Zero" $ do
    cType shouldTrace ii g n VNat
    let nVal = cEval shouldTrace n (v, [])
    unless  (quote0 nVal == quote0 mVal)
            (throwError "number mismatch FZero")
cType shouldTrace ii g@(v,t) (FSucc n f') (VFin (VSucc mVal))
  = traceIf shouldTrace "cType fin succ" $ do
    cType shouldTrace ii g n VNat
    let nVal = cEval shouldTrace n (v,[])
    unless  (quote0 nVal == quote0 mVal)
            (throwError "number mismatch FSucc")
    cType shouldTrace ii g f' (VFin mVal)
cType shouldTrace ii g a v
  = throwError $ "type mismatch - (unimplemented?) \n" <>
                 "given: " <> render (cPrint 0 0 (quote0 (cEval shouldTrace a (fst g, []))))
             <> " type expected: " <> render (cPrint 0 0 (quote0 v)) <> "\n"

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c')     =  Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii r  Star           =  Star
iSubst ii r  (Pi ty ty')    =  Pi  (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j)      =  if ii == j then i' else Bound j
iSubst ii i' (Free y)       =  Free y
iSubst ii i' (i :$: c)      =  (iSubst ii i' i) :$: (cSubst ii i' c)
iSubst ii r  Nat            =  Nat
iSubst ii r  (NatElim m mz ms n)
                            =  NatElim (cSubst ii r m)
                                       (cSubst ii r mz) (cSubst ii r ms)
                                       (cSubst ii r n)
iSubst ii r  (Vec a n)      =  Vec (cSubst ii r a) (cSubst ii r n)
iSubst ii r  (VecElim a m mn mc n xs)
                            =  VecElim (cSubst ii r a) (cSubst ii r m)
                                       (cSubst ii r mn) (cSubst ii r mc)
                                       (cSubst ii r n) (cSubst ii r xs)
iSubst ii r  (Eq a x y)     =  Eq (cSubst ii r a)
                                     (cSubst ii r x) (cSubst ii r y)
iSubst ii r  (EqElim a m mr x y eq)
                            =  EqElim (cSubst ii r a) (cSubst ii r m)
                                        (cSubst ii r mr) (cSubst ii r x)
                                        (cSubst ii r y) (cSubst ii r eq)
iSubst ii r  (Fin n)        =  Fin (cSubst ii r n)
iSubst ii r  (FinElim m mz ms n f)
                            =  FinElim (cSubst ii r m)
                                        (cSubst ii r mz) (cSubst ii r ms)
                                        (cSubst ii r n) (cSubst ii r f)
iSubst ii r Poly             = Poly
iSubst ii r (PolyElim m t a) = PolyElim (cSubst ii r m) (cSubst ii r t) (cSubst ii r a)
iSubst ii r (Sigma f s)      = Sigma (cSubst ii r f)(cSubst ii r s)
iSubst ii r (SigElim t1 t2 m f p)
                             = SigElim (cSubst ii r t1) (cSubst ii r t2)
                                       (cSubst ii r m) (cSubst ii r f)
                                       (cSubst ii r p)
iSubst ii r IBool            = IBool
iSubst ii r IFalse           = IFalse
iSubst ii r ITrue            = ITrue

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)      = Inf (iSubst ii i' i)
cSubst ii i' (Lam c)      = Lam (cSubst (ii + 1) i' c)
cSubst ii r  Zero         = Zero
cSubst ii r  (Succ n)     = Succ (cSubst ii r n)
cSubst ii r  (Nil a)      = Nil (cSubst ii r a)
cSubst ii r  (Cons a n x xs)
                          = Cons (cSubst ii r a) (cSubst ii r n)
                                 (cSubst ii r x) (cSubst ii r xs)
cSubst ii r  (Refl a x)   = Refl (cSubst ii r a) (cSubst ii r x)
cSubst ii r  (FZero n)    = FZero (cSubst ii r n)
cSubst ii r  (FSucc n k)  = FSucc (cSubst ii r n) (cSubst ii r k)
cSubst ii r  CTrue        = CTrue
cSubst ii r  CFalse       = CFalse
cSubst ii r  (MkPoly s p) = MkPoly (cSubst ii r s) (cSubst ii r p)
cSubst ii r  (Comma t1 t2 v1 v2)
                          = Comma (cSubst ii r t1) (cSubst ii r t2)
                                  (cSubst ii r v1) (cSubst ii r v2)

