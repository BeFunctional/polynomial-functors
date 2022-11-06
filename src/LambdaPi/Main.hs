module LambdaPi.Main where

import Common
import REPL

import LambdaPi.AST
import LambdaPi.Eval
import LambdaPi.Check
import LambdaPi.Quote
import LambdaPi.Parser
import LambdaPi.Printer

import Debug.Trace

lpte :: Ctx Value
lpte =      [(Global "Zero", VNat),
             (Global "Succ", VPi VNat (\_ -> VNat)),
             (Global "Nat", VStar),
             (Global "natElim", VPi (VPi VNat (\_ -> VStar)) (\m ->
                               VPi (m `vapp` VZero) (\_ ->
                               VPi (VPi VNat (\ k -> VPi (m `vapp` k) (\_ -> (m `vapp` (VSucc k))))) (\_ ->
                               VPi VNat (\ n -> m `vapp` n))))),
             (Global "Type", VStar),
             ------------------------------------------------------
             -- Polynomial things
             ------------------------------------------------------
             (Global "Poly", VStar), -- Poly is a type
             (Global "MkPoly", VPi VStar (\s -> VPi (VPi s (const VStar)) (const VPoly))),
             (Global "polyElim", VPi (VPi VPoly (const VStar)) (\motive ->    -- motive
                                 VPi (VPi VStar (\sh ->                       -- \
                                       VPi (VPi sh (const VStar)) (\pos ->    --  -eliminator
                                       motive `vapp` VMkPoly sh pos))) (\_ -> -- /
                                 VPi VPoly (\c ->                             -- argument
                                 motive `vapp` c)))),                         -- return type
             ------------------------------------------------------
             -- Sigma types
             ------------------------------------------------------
             (Global "Sigma", VPi VStar (\x -> VPi (VPi x (const VStar)) (const VStar))),
             (Global "MkSigma", VPi VStar                      (\fstTy -> VPi
                                     (VPi fstTy (const VStar)) (\sndTy -> VPi
                                     fstTy                     (\val1 -> VPi
                                     (sndTy `vapp` val1)       (\val2 ->
                                     VSigma fstTy sndTy))))),
             -- z : Σ[x : A1] A2            x : A1, y : A2 ⊢ b : B(x, y)
             -- --------------------------------------------------------
             --     match z of (x, y) => b : B(z)

             -- sigElim : (ty : Type) ->
             --           (fy : ty -> Type) ->
             --           (m : Sigma ty fy -> Type)
             --           (i : (x : ty) -> (y : fy x) -> m (MkSigma x y))
             --           (s : Sigma ty fy)
             --           m s
             (Global "sigElim", VPi VStar                               (\ty -> VPi
                                     (VPi ty (const VStar))             (\fy -> VPi
                                     (VPi (VSigma ty fy) (const VStar)) (\m -> VPi
                                     (VPi ty            (\x ->
                                      VPi (fy `vapp` x) (\y ->
                                        m `vapp` VComma ty fy x y)))    (\i -> VPi
                                     (VSigma ty fy)                     (\s ->
                                     m `vapp` s)))))),
             ------------------------------------------------------
             -- List things
             ------------------------------------------------------
             (Global "Nil", VPi VStar (\ a -> VVec a VZero)),
             (Global "Cons", VPi VStar (\ a ->
                            VPi VNat (\ n ->
                            VPi a (\_ -> VPi (VVec a n) (\_ -> VVec a (VSucc n)))))),
             (Global "Vec", VPi VStar (\_ -> VPi VNat (\_ -> VStar))),
             (Global "vecElim", VPi VStar (\ a ->
                               VPi (VPi VNat (\ n -> VPi (VVec a n) (\_ -> VStar))) (\ m ->
                               VPi (m `vapp` VZero `vapp` (VNil a)) (\_ ->
                               VPi (VPi VNat (\ n ->
                                     VPi a (\ x ->
                                     VPi (VVec a n) (\ xs ->
                                     VPi (m `vapp` n `vapp` xs) (\_ ->
                                     m `vapp` VSucc n `vapp` VCons a n x xs))))) (\_ ->
                               VPi VNat (\ n ->
                               VPi (VVec a n) (\ xs -> m `vapp` n `vapp` xs))))))),
             ------------------------------------------------------
             -- Equality
             ------------------------------------------------------
             (Global "Refl", VPi VStar (\ a -> VPi a (\ x ->
                            VEq a x x))),
             (Global "Eq", VPi VStar (\ a -> VPi a (\ x -> VPi a (\y -> VStar)))),
             (Global "eqElim", VPi VStar (\ a ->
                              VPi (VPi a (\ x -> VPi a (\ y -> VPi (VEq a x y) (\_ -> VStar)))) (\m ->
                              VPi (VPi a (\ x -> ((m `vapp` x) `vapp` x) `vapp` VRefl a x))     (\_ ->
                              VPi a (\ x -> VPi a (\ y ->
                              VPi (VEq a x y) (\ eq ->
                              ((m `vapp` x) `vapp` y) `vapp` eq))))))),
             ------------------------------------------------------
             -- Bool things
             ------------------------------------------------------
             (Global "Bool", VStar),
             (Global "True", VBool),
             (Global "False", VBool),
             (Global "if", (VPi (VPi VBool (const VStar)) (\m -> VPi
                                (m `vapp` VTrue) (\th -> VPi
                                (m `vapp` VFalse) (\el -> VPi
                                VBool (\b ->
                                m `vapp` b)))))),
             ------------------------------------------------------
             -- Finite things
             ------------------------------------------------------
             (Global "FZero", VPi VNat (\ n -> VFin (VSucc n))),
             (Global "FSucc", VPi VNat (\ n -> VPi (VFin n) (\ f ->
                              VFin (VSucc n)))),
             (Global "Fin", VPi VNat (\ n -> VStar)),
             (Global "finElim", VPi (VPi VNat (\ n -> VPi (VFin n) (\_ -> VStar))) (\ m ->
                                VPi (VPi VNat (\ n -> m `vapp` (VSucc n) `vapp` (VFZero n))) (\_ ->
                                VPi (VPi VNat                  (\n ->
                                     VPi (VFin n)              (\f ->
                                     VPi (m `vapp` n `vapp` f) (\_ ->
                                     m `vapp` (VSucc n) `vapp` (VFSucc n f))))) (\_ ->
                                VPi VNat (\ n -> VPi (VFin n) (\ f ->
                                m `vapp` n `vapp` f))))))]

data FullContext = FullContext { types :: Ctx Value, values :: Ctx Value }

lpve :: Ctx Value
lpve =      [(Global "Zero", VZero),
             (Global "Succ", VLam (\ n -> VSucc n)),
             (Global "Nat", VNat),
             (Global "natElim", cEval False (Lam (Lam (Lam (Lam (Inf (NatElim (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))) ([], [])),
             (Global "Type", VStar),
             (Global "Poly", VPoly), -- The value for the type Poly
             (Global "MkPoly", VLam (\ty -> VLam (\fy -> VMkPoly ty fy))), -- poly constructor
             (Global "polyElim",
               cEval False
                     (Lam $ Lam $ Lam $ Inf $
                      PolyElim (Inf (Bound 2))
                               (Inf (Bound 1))
                               (Inf (Bound 0))
                      ) ([],[])),
             (Global "Sigma", VLam (\a -> VLam (\b -> VSigma a b))),
             (Global "MkSigma", VLam (\a -> VLam
                                     (\b -> VLam
                                     (\v1 -> VLam
                                     (\v2 -> VComma a b v1 v2))))),
             (Global "sigElim", cEval False (Lam $ Lam $ Lam $ Lam $ Lam $
                 Inf (SigElim (Inf (Bound 4))
                              (Inf (Bound 3))
                              (Inf (Bound 2))
                              (Inf (Bound 1))
                              (Inf (Bound 0)))
                 ) ([],[])),

             (Global "Bool", VBool),
             (Global "True", VTrue),
             (Global "False", VFalse),
             (Global "if", cEval False (Lam $ Lam $ Lam $ Lam $
                 Inf (If (Inf (Bound 3))
                         (Inf (Bound 2))
                         (Inf (Bound 1))
                         (Inf (Bound 0)))
                 ) ([],[])),
             (Global "Nil", VLam (\ a -> VNil a)),
             (Global "Cons", VLam (\ a -> VLam (\ n -> VLam (\ x -> VLam (\ xs ->
                             VCons a n x xs))))),
             (Global "Vec", VLam (\ a -> VLam (\ n -> VVec a n))),
             (Global "vecElim", cEval False (Lam (Lam (Lam (Lam (Lam (Lam (Inf (VecElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "Refl", VLam (\ a -> VLam (\ x -> VRefl a x))),
             (Global "Eq", VLam (\ a -> VLam (\ x -> VLam (\ y -> VEq a x y)))),
             (Global "eqElim", cEval False (Lam (Lam (Lam (Lam (Lam (Lam (Inf (EqElim (Inf (Bound 5)) (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0)))))))))) ([],[])),
             (Global "FZero", VLam (\ n -> VFZero n)),
             (Global "FSucc", VLam (\ n -> VLam (\ f -> VFSucc n f))),
             (Global "Fin", VLam (\ n -> VFin n)),
             (Global "finElim", cEval False (Lam (Lam (Lam (Lam (Lam (Inf (FinElim (Inf (Bound 4)) (Inf (Bound 3)) (Inf (Bound 2)) (Inf (Bound 1)) (Inf (Bound 0))))))))) ([],[]))]


lpassume state@(out, ve, te) x t =
  -- t: CTerm
  check lp (show . cPrint 0 0 . quote0) state x (Ann t (Inf Star))
        (\ (y, v) -> return ()) --  putStrLn (render (text x <> text " :: " <> cPrint 0 0 (quote0 v))))
        (\ (y, v) -> (out, ve, (Global x, v) : te))
printNameContext :: NameEnv Value -> String
printNameContext = unlines . fmap (\(Global nm, ty) -> nm ++ ": " ++ show (cPrint 0 0 (quote0 ty)))

printTypeContext :: Ctx Value -> String
printTypeContext = unlines . fmap (\(Global nm, vl) -> nm ++ ":= " ++ show (cPrint 0 0 (quote0 vl)))

lp :: Interpreter ITerm CTerm Value Value CTerm Value
lp = I { iname = "lambda-Pi",
         iprompt = "LP> ",
         iitype = \ v c i -> iType False 0 (v, c) i,
         iquote = quote0,
         ieval = \ e x -> iEval False x (e, []),
         ihastype = id,
         icprint = cPrint 0 0,
         itprint = cPrint 0 0 . quote0,
         iiparse = parseITerm 0 [],
         isparse = parseStmt [],
         iassume = \ s (x, t) -> lpassume s x t }

checkSimple :: State Value Value
            -> ITerm
            -> ((Value, Value) -> State Value Value)
            -> (State Value Value)
checkSimple state@(out, oldValueContext, oldTypeContext) term updateState =
                  --  typecheck and evaluate
                  let x = iType False 0 (oldValueContext, oldTypeContext) term in
                  case x of
                    -- error, do not update the state
                    Left error -> state
                    -- success, update the state, print the new result
                    Right y   ->
                        let v = iEval False term (oldValueContext, [])
                        in (updateState (y, v))

checkPure :: State Value Value -> ITerm
         -> ((Value, Value) -> State Value Value)
         -> Either String (State Value Value)
checkPure state@(out, ve, te) t k =
                do
                  -- i: String, t: Type
                  --  typecheck and evaluate
                  x <- iType False 0 (te, ve) t
                  let v = iEval False t (ve, [])
                  return (k (x, v))

-- checkAdd :: State Value Value -> String -> ITerm -> Either String (State Value Value)
-- checkAdd state@(nm, valueCtx, typeCtx) identifier term =
--   checkPure state term (\(newTy, newVal) -> (nm, (Global identifier, newVal) : valueCtx,
--                                                  (Global identifier, newTy) : typeCtx))

repLP :: IO ()
repLP = readevalprint Nothing lp ([], lpve, lpte)

runInteractive :: String -> IO ()
runInteractive stdlib = readevalprint (Just stdlib) lp ([], lpve, lpte)

main :: IO ()
main = repLP
