module LambdaPi.Main where

import Common
import REPL

import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Check
import LambdaPi.Quote
import LambdaPi.Parser
import LambdaPi.Printer

lpte :: Ctx Value_
lpte =      [(Global "Zero", VNat_),
             (Global "Succ", VPi_ VNat_ (\ _ -> VNat_)),
             (Global "Nat", VStar_),
             (Global "Type", VStar_),
             -- natElim : (m : Nat -> Type) ->
             --           (m Z) ->
             --           ((k : Nat) -> m k -> m (S k)) ->
             --           (n : Nat) ->
             --           m n
             (Global "natElim", VPi_ (VPi_ VNat_ (\ _ -> VStar_)) (\ m ->
                               VPi_ (m `vapp_` VZero_) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ k -> VPi_ (m `vapp_` k) (\ _ -> (m `vapp_` (VSucc_ k))))) ( \ _ ->
                               VPi_ VNat_ (\ n -> m `vapp_` n))))),
             (Global "MkPoly", VPi_ VStar_ (\s -> VPi_ (VPi_ s (const VStar_)) (const VPoly_))),
             (Global "polyElim", VPi_ (VPi_ VPoly_ (const VStar_)) (\motive -> -- motive
                                 VPi_ (VPi_ VStar_ (\sh ->
                                       VPi_ (VPi_ sh (const VStar_)) (\pos ->
                                       motive `vapp_` VMkPoly_ sh pos))) (\_ ->    -- eliminator
                                 VPi_ VPoly_ (\c ->                            -- argument
                                 motive `vapp_` c)))),                          -- return type
             (Global "Sigma", VPi_ VStar_ (\x -> VPi_ (VPi_ x (const VStar_)) (const VStar_))),
             (Global "MkSigma", VPi_ VStar_ (\x -> VPi_
                                     (VPi_ x (const VStar_)) (\f -> VPi_
                                     x (\p1 -> VPi_
                                     (f `vapp_` p1) (\p2 ->
                                     VComma_ x f))))),
             -- z : Σ[x : A1] A2            x : A1, y : A2 ⊢ b : B(x, y)
             -- --------------------------------------------------------
             --     match z of (x, y) => b : B(z)

             -- sigElim : (ty : Type) ->
             --           (fy : ty -> Type) ->
             --           (m : (x : ty) -> fy x -> Type)
             --           (i : (x : ty) -> (y : fy x) -> m x y)
             --           (s : Sigma ty fy)
             --           m s
             (Global "sigElim", VPi_ VStar_ (\ty -> VPi_
                                     (VPi_ ty (const VStar_)) (\fy -> VPi_
                                     (VPi_ (VSigma_ ty fy) (const VStar_)) (\m -> VPi_
                                     (VPi_ ty (\x -> VPi_ (fy `vapp_` x) (\y -> m `vapp_` VComma_ x y))) (\i -> VPi_
                                     (VSigma_ ty fy) (\s -> m `vapp_` s)))))),
             (Global "Nil", VPi_ VStar_ (\ a -> VVec_ a VZero_)),
             (Global "Cons", VPi_ VStar_ (\ a ->
                            VPi_ VNat_ (\ n ->
                            VPi_ a (\ _ -> VPi_ (VVec_ a n) (\ _ -> VVec_ a (VSucc_ n)))))),
             (Global "Vec", VPi_ VStar_ (\ _ -> VPi_ VNat_ (\ _ -> VStar_))),
             (Global "vecElim", VPi_ VStar_ (\ a ->
                               VPi_ (VPi_ VNat_ (\ n -> VPi_ (VVec_ a n) (\ _ -> VStar_))) (\ m ->
                               VPi_ (m `vapp_` VZero_ `vapp_` (VNil_ a)) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ n ->
                                     VPi_ a (\ x ->
                                     VPi_ (VVec_ a n) (\ xs ->
                                     VPi_ (m `vapp_` n `vapp_` xs) (\ _ ->
                                     m `vapp_` VSucc_ n `vapp_` VCons_ a n x xs))))) (\ _ ->
                               VPi_ VNat_ (\ n ->
                               VPi_ (VVec_ a n) (\ xs -> m `vapp_` n `vapp_` xs))))))),
             (Global "Refl", VPi_ VStar_ (\ a -> VPi_ a (\ x ->
                            VEq_ a x x))),
             (Global "Eq", VPi_ VStar_ (\ a -> VPi_ a (\ x -> VPi_ a (\ y -> VStar_)))),
             (Global "eqElim", VPi_ VStar_ (\ a ->
                              VPi_ (VPi_ a (\ x -> VPi_ a (\ y -> VPi_ (VEq_ a x y) (\ _ -> VStar_)))) (\ m ->
                              VPi_ (VPi_ a (\ x -> ((m `vapp_` x) `vapp_` x) `vapp_` VRefl_ a x)) (\ _ ->
                              VPi_ a (\ x -> VPi_ a (\ y ->
                              VPi_ (VEq_ a x y) (\ eq ->
                              ((m `vapp_` x) `vapp_` y) `vapp_` eq))))))),
             (Global "FZero", VPi_ VNat_ (\ n -> VFin_ (VSucc_ n))),
             (Global "FSucc", VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f ->
                             VFin_ (VSucc_ n)))),
             (Global "Fin", VPi_ VNat_ (\ n -> VStar_)),
             (Global "finElim", VPi_ (VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ _ -> VStar_))) (\ m ->
                               VPi_ (VPi_ VNat_ (\ n -> m `vapp_` (VSucc_ n) `vapp_` (VFZero_ n))) (\ _ ->
                               VPi_ (VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f -> VPi_ (m `vapp_` n `vapp_` f) (\ _ -> m `vapp_` (VSucc_ n) `vapp_` (VFSucc_ n f))))) (\ _ ->
                               VPi_ VNat_ (\ n -> VPi_ (VFin_ n) (\ f ->
                               m `vapp_` n `vapp_` f))))))]

lpve :: Ctx Value_
lpve =      [(Global "Zero", VZero_),
             (Global "Succ", VLam_ (\ n -> VSucc_ n)),
             (Global "Nat", VNat_),
             (Global "natElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (NatElim_ (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))) ([], [])),
             (Global "Poly", VPoly_),
             (Global "Type", VStar_),
             (Global "Nil", VLam_ (\ a -> VNil_ a)),
             (Global "Cons", VLam_ (\ a -> VLam_ (\ n -> VLam_ (\ x -> VLam_ (\ xs ->
                            VCons_ a n x xs))))),
             (Global "Vec", VLam_ (\ a -> VLam_ (\ n -> VVec_ a n))),
             (Global "vecElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (VecElim_ (Inf_ (Bound_ 5)) (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))))) ([],[])),
             (Global "Refl", VLam_ (\ a -> VLam_ (\ x -> VRefl_ a x))),
             (Global "Eq", VLam_ (\ a -> VLam_ (\ x -> VLam_ (\ y -> VEq_ a x y)))),
             (Global "eqElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (EqElim_ (Inf_ (Bound_ 5)) (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0)))))))))) ([],[])),
             (Global "FZero", VLam_ (\ n -> VFZero_ n)),
             (Global "FSucc", VLam_ (\ n -> VLam_ (\ f -> VFSucc_ n f))),
             (Global "Fin", VLam_ (\ n -> VFin_ n)),
             (Global "finElim", cEval_ (Lam_ (Lam_ (Lam_ (Lam_ (Lam_ (Inf_ (FinElim_ (Inf_ (Bound_ 4)) (Inf_ (Bound_ 3)) (Inf_ (Bound_ 2)) (Inf_ (Bound_ 1)) (Inf_ (Bound_ 0))))))))) ([],[]))]

lpassume state@(out, ve, te) x t =
  -- x: String, t: CTerm
  check lp state x (Ann_ t (Inf_ Star_))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint_ 0 0 (quote0_ v))))
        (\ (y, v) -> (out, ve, (Global x, v) : te))

lp :: Interpreter ITerm_ CTerm_ Value_ Value_ CTerm_ Value_
lp = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c -> iType_ 0 (v, c),
         iquote = quote0_,
         ieval = \ e x -> iEval_ x (e, []),
         ihastype = id,
         icprint = cPrint_ 0 0,
         itprint = cPrint_ 0 0 . quote0_,
         iiparse = parseITerm_ 0 [],
         isparse = parseStmt_ [],
         iassume = \ s (x, t) -> lpassume s x t }

repLP :: IO ()
repLP = readevalprint lp ([], lpve, lpte)

main :: IO ()
main = repLP