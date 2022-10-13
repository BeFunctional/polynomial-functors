module LambdaPi.Check where

import Control.Monad.Except

import Text.PrettyPrint.HughesPJ hiding (parens)

import Common
import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Quote
import LambdaPi.Printer

iType0 :: (NameEnv Value,Context) -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> (NameEnv Value,Context) -> ITerm -> Result Type
iType ii g (Ann e tyt)
  = do cType  ii g tyt VStar
       let ty = cEval tyt (fst g, [])
       cType ii g e ty
       return ty
iType ii g Star
   = return VStar
iType ii g (Pi tyt tyt')
   = do cType ii g tyt VStar
        let ty = cEval tyt (fst g, [])
        cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty) : g))) g)
                  (cSubst 0 (Free (Local ii)) tyt') VStar
        return VStar
iType ii g (Free x)
  =     case lookup x (snd g) of
          Just ty        ->  return ty
          Nothing        ->  throwError ("unknown identifier: " ++ render (iPrint 0 0 (Free x)))
iType ii g (e1 :$: e2)
  =     do  si <- iType ii g e1
            case si of
              VPi  ty ty1 -> do cType ii g e2 ty
                                return ( ty1 (cEval e2 (fst g, [])))
              _           -> throwError $ "illegal application : " ++ show e2 ++ "applyed to " ++ show e1
iType ii g Nat                  =  return VStar
iType ii g (NatElim m mz ms n)  =
  do  cType ii g m (VPi VNat (const VStar))
      let mVal  = cEval m (fst g, [])
      cType ii g mz (mVal `vapp` VZero)
      cType ii g ms (VPi VNat (\k -> VPi (mVal `vapp` k) (\_ -> mVal `vapp` VSucc k)))
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      return (mVal `vapp` nVal)

iType ii g (Sigma f s)      = do
  cType ii g f VStar
  let fVal = cEval f (fst g, [])
  cType ii g s (VPi fVal (const VStar))
  return VStar
iType ii g (SigElim ty fty m f p) = do
  cType ii g ty VStar
  let tyVal = cEval ty (fst g, [])
  sig <- cType ii g fty (VPi tyVal (const VStar))
  let fyVal = cEval fty (fst g, [])
  -- m : Sigma ty fy -> Type
  cType ii g m (VPi (VSigma tyVal fyVal) (const VStar))
  let mVal = cEval m (fst g, [])
  cType ii g f (VPi (VSigma tyVal fyVal) (\sig -> mVal `vapp` sig))
  cType ii g p (VSigma tyVal fyVal)
  let product = cEval p (fst g, [])
  return $ mVal `vapp` product

iType ii g Poly             = return VStar -- Poly is a type
iType ii g (PolyElim m f c) =
  do cType ii g m (VPi VPoly (\_ -> VStar)) -- check the motive
     let mVal = cEval m (fst g, []) -- quote the motive
     cType ii g c VPoly -- check the argument
     -- check the elimination function whose type depends on both arguments
     cType ii g f (VPi VStar (\shapes ->
                    VPi (VPi shapes (const VStar)) (\positions ->
                    mVal `vapp` VMkPoly shapes positions)))
     let cVal = cEval c (fst g, []) -- quote the container
     return (mVal `vapp` cVal)

iType ii g (Vec a n) =
  do  cType ii g a  VStar
      cType ii g n  VNat
      return VStar
iType ii g (VecElim a m mn mc n vs) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      cType ii g m
        (  VPi VNat (\n -> VPi (VVec aVal n) (\_ -> VStar)))
      let mVal = cEval m (fst g, [])
      cType ii g mn (foldl vapp mVal [VZero, VNil aVal])
      cType ii g mc
        (  VPi VNat (\ n ->
           VPi aVal (\ y ->
           VPi (VVec aVal n) (\ ys ->
           VPi (foldl vapp mVal [n, ys]) (\_ ->
           (foldl vapp mVal [VSucc n, VCons aVal n y ys]))))))
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      cType ii g vs (VVec aVal nVal)
      let vsVal = cEval vs (fst g, [])
      return (foldl vapp mVal [nVal, vsVal])
iType i g (Eq a x y) =
  do  cType i g a VStar
      let aVal = cEval a (fst g, [])
      cType i g x aVal
      cType i g y aVal
      return VStar
iType i g (EqElim a m mr x y eq) =
  do  cType i g a VStar
      let aVal = cEval a (fst g, [])
      cType i g m
        (VPi aVal (\ x ->
         VPi aVal (\ y ->
         VPi (VEq aVal x y) (\_ -> VStar))))
      let mVal = cEval m (fst g, [])
      cType i g mr
        (VPi aVal (\ x ->
         foldl vapp mVal [x, x, VRefl aVal x]))
      cType i g x aVal
      let xVal = cEval x (fst g, [])
      cType i g y aVal
      let yVal = cEval y (fst g, [])
      cType i g eq (VEq aVal xVal yVal)
      let eqVal = cEval eq (fst g, [])
      return (foldl vapp mVal [xVal, yVal, eqVal])
iType ii g (Fin n) =
  do  cType ii g n VNat
      return VStar
iType ii g (FinElim m mz ms n f) =
  do  cType ii g m (VPi VNat (\k -> VPi (VFin k) (const VStar)))
      let mVal  = cEval m (fst g, [])
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      cType ii g mz (VPi VNat (\k -> mVal `vapp` VSucc k `vapp` VFZero k))
      cType ii g ms (VPi VNat (\k ->
          VPi (VFin k) (\fk ->
              VPi (mVal `vapp` k `vapp` fk) (\_ ->
                  mVal `vapp` VSucc k `vapp` VFSucc k fk))))
      cType ii g f (VFin nVal)
      let fVal = cEval f (fst g, [])
      return (mVal `vapp` nVal `vapp` fVal)
iType _ _ tm = throwError $ "No type match for " ++ render (iPrint 0 0 tm)

cType :: Int -> (NameEnv Value,Context) -> CTerm -> Type -> Result ()
cType ii g (Inf e) v
  =     do  v' <- iType ii g e
            unless ( quote0 v == quote0 v')
                   (throwError ("type mismatch:\n"
                             ++ "type inferred:  "
                             ++ render (cPrint 0 0 (quote0 v')) ++ "\n"
                             ++ "type expected:  " ++ render (cPrint 0 0 (quote0 v)) ++ "\n"
                             ++ "for expression: " ++ render (iPrint 0 0 e)))
cType ii g (Lam e) ( VPi ty ty')
  =     cType  (ii + 1) ((\ (d,g) -> (d,  ((Local ii, ty ) : g))) g)
                (cSubst 0 (Free (Local ii)) e) ( ty' (vfree (Local ii)))
cType ii g Zero      VNat  =  return ()
cType ii g (Succ k)  VNat  =  cType ii g k VNat
cType ii g (Comma ty sy x f) (VSigma ty' fy') = do
  let xVal = cEval x (fst g, [])
  unless (quote0 xVal == quote0 ty')
         (throwError $ "type mismatch:\n"
                    ++ "given: " ++ render (cPrint 0 0 (quote0 xVal)) ++ "\n"
                    ++ "expected: " ++ render (cPrint 0 0 (quote0 ty')) ++ "\n")

cType ii g (MkPoly x f) VPoly =
  do cType ii g x VStar -- check if the first argument is a type
     let xVal = cEval x (fst g, [])
     cType ii g f (VPi xVal (const VStar)) -- check if the second argument is a Π
cType ii g (Nil a) (VVec bVal VZero) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
cType ii g (Cons a n x xs) (VVec bVal (VSucc k)) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
      cType ii g n VNat
      let nVal = cEval n (fst g, [])
      unless  (quote0 nVal == quote0 k)
              (throwError "number mismatch")
      cType ii g x aVal
      cType ii g xs (VVec bVal k)
cType ii g (Refl a z) (VEq bVal xVal yVal) =
  do  cType ii g a VStar
      let aVal = cEval a (fst g, [])
      unless  (quote0 aVal == quote0 bVal)
              (throwError "type mismatch")
      cType ii g z aVal
      let zVal = cEval z (fst g, [])
      unless  (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
              (throwError "type mismatch")
cType ii g@(v,t) (FZero n) (VFin (VSucc mVal)) =
  do
    cType ii g n VNat
    let nVal = cEval n (v, [])
    unless  (quote0 nVal == quote0 mVal)
            (throwError "number mismatch FZero")
cType ii g@(v,t) (FSucc n f') (VFin (VSucc mVal)) =
  do
    cType ii g n VNat
    let nVal = cEval n (v,[])
    unless  (quote0 nVal == quote0 mVal)
            (throwError "number mismatch FSucc")
    cType ii g f' (VFin mVal)
cType ii g a v
  = throwError $ "type mismatch - (unimplemented?) \n" ++
                 "given: " ++ render (cPrint 0 0 (quote0 (cEval a (fst g, []))))
             ++ " type expected: " ++ render (cPrint 0 0 (quote0 v)) ++ "\n"

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i'   (Ann c c')     =  Ann (cSubst ii i' c) (cSubst ii i' c')

iSubst ii r  Star           =  Star
iSubst ii r  (Pi ty ty')    =  Pi  (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j)      =  if ii == j then i' else Bound j
iSubst ii i' (Free y)       =  Free y
iSubst ii i' (i :$: c)       =  (iSubst ii i' i) :$: (cSubst ii i' c)
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
iSubst ii r (Poly) = Poly
iSubst ii r v = error $ "unhandled substitution: " ++ show v

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
cSubst ii r  CTrue         = CTrue
cSubst ii r  CFalse        = CFalse
