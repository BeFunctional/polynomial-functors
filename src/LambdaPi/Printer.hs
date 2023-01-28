module LambdaPi.Printer where

import Prelude hiding ((<>))
import Text.PrettyPrint.HughesPJ hiding (parens, text)

import Common
import LambdaPi.AST

iPrint :: Int -> Int -> ITerm -> Doc
iPrint p ii (Ann c ty)       =  parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> cPrint 0 ii ty)
iPrint p ii Star             =  text "*"
iPrint p ii (Pi d (Inf (Pi d' r)))
                             =  parensIf (p > 0) (nestedForall (ii + 2) [(ii + 1, d'), (ii, d)] r)
iPrint p ii (Pi d r)         =  parensIf (p > 0) (sep [text "forall " <> text (vars !! ii) <> text " :: " <> cPrint 0 ii d <> text " .", cPrint 0 (ii + 1) r])
iPrint p ii (Bound k)        =  text (vars !! (ii - k - 1))
iPrint p ii (Free (Global s))=  text s
iPrint p ii (i :$: c)        =  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint p ii Nat              =  text "Nat"
iPrint p ii (NatElim m z s n)=  iPrint p ii (Free (Global "natElim") :$: m :$: z :$: s :$: n)
iPrint p ii (Vec a n)        =  iPrint p ii (Free (Global "Vec") :$: a :$: n)
iPrint p ii (VecElim a m mn mc n xs)
                             =  iPrint p ii (Free (Global "vecElim") :$: a :$: m :$: mn :$: mc :$: n :$: xs)
iPrint p ii (Eq a x y)       =  iPrint p ii (Free (Global "Eq") :$: a :$: x :$: y)
iPrint p ii (EqElim a m mr x y eq)
                             =  iPrint p ii (Free (Global "eqElim") :$: a :$: m :$: mr :$: x :$: y :$: eq)
iPrint p ii (Fin n)          =  iPrint p ii (Free (Global "Fin") :$: n)
iPrint p ii (FinElim m mz ms n f)
                             =  iPrint p ii (Free (Global "finElim") :$: m :$: mz :$: ms :$: n :$: f)
iPrint p ii (PolyElim x y z) =  iPrint p ii (Free (Global "polyElim") :$: x :$: y :$: z)
iPrint p ii (Sigma (Inf IBool) b@(Lam (Inf (If motive thn els (Inf (Bound 0))))))  =
  -- if isConst 0 motive
  -- then text "Either" <+> cPrint p (ii + 1) thn <+> cPrint p (ii + 1) els
  -- else
  iPrint p ii (Free (Global "Sigma") :$: (Inf IBool) :$: b)
iPrint p ii (Sigma x y)      =
  -- if isConst 0 y
  -- then lparen <> cPrint p ii x <> comma <+> cPrint p ii y <> rparen
  -- else
  iPrint p ii (Free (Global "Sigma") :$: x :$: y)
iPrint p ii (SigElim c y m f v)
                             =  if (isConst 0 f) && (isConst 1 f) -- if the return does not use its arguments
                                then cPrint p ii f
                                else iPrint p ii (Free (Global "SigElim") :$: c :$: y :$: m :$: f :$: v)
iPrint p ii IBool            =  text "Bool"
iPrint p ii (If motive thn els arg)
                             = text "if" <+> cPrint p ii arg <+>
                               text "then" <+> cPrint p ii thn <+>
                               text "else" <+> cPrint p ii els
iPrint p ii x                = text "[" <> text (tshow x) <> text "]"

cPrint :: Int -> Int -> CTerm -> Doc
cPrint p ii (Inf i)      = iPrint p ii i
cPrint p ii (Lam c)      = if isConst 0 c
    then parensIf (p > 0) (cPrint 0 (ii + 1) c)
    else parensIf (p > 0) (text "\\ " <> text (vars !! ii) <> text " -> " <> cPrint 0 (ii + 1) c)
cPrint p ii Zero         = fromNat 0 ii Zero     --  text "Zero"
cPrint p ii (Succ n)     = fromNat 0 ii (Succ n) --  iPrint p ii (Free (Global "Succ") :$: n)
cPrint p ii (Nil a)      = iPrint p ii (Free (Global "Nil") :$: a)
cPrint p ii (Cons a n x xs)
                         = iPrint p ii (Free (Global "Cons") :$: a :$: n :$: x :$: xs)
cPrint p ii (Refl a x)   = iPrint p ii (Free (Global "Refl") :$: a :$: x)
cPrint p ii (FZero n)    = iPrint p ii (Free (Global "FZero") :$: n)
cPrint p ii (FSucc n f)  = iPrint p ii (Free (Global "FSucc") :$: n :$: f)
cPrint p ii (MkPoly x y) = iPrint p ii (Free (Global "MkPoly") :$: x :$: y)
cPrint p ii (Comma ty sy x y)
                         = iPrint p ii (Free (Global "MkSigma") :$: ty :$: sy :$: x :$: y)
cPrint p ii CTrue        = text "True"
cPrint p ii CFalse       = text "False"

fromNat :: Int -> Int -> CTerm -> Doc
fromNat n ii Zero = int n
fromNat n ii (Succ k) = fromNat (n + 1) ii k
fromNat n ii t = parensIf True (int n <> text " + " <> cPrint 0 ii t)

nestedForall :: Int -> [(Int, CTerm)] -> CTerm -> Doc
nestedForall ii ds (Inf (Pi d r)) = nestedForall (ii + 1) ((ii, d) : ds) r
nestedForall ii ds x
  = sep [text "forall " <> sep [parensIf True (text (vars !! n) <> text " :: " <> cPrint 0 n d)
                               | (n,d) <- reverse ds] <> text " .", cPrint 0 ii x]

isIConst :: Int -> ITerm -> Bool
isIConst i (Bound n) = i /= n
isIConst i (Ann val ty) = isConst i val && isConst i ty
isIConst i (Pi inp out) = isConst i inp && isConst (i + 1) out
isIConst i (fn :$: arg) = isIConst i fn && isConst i arg
isIConst i (NatElim motive zero succ val)
  = isConst i motive
  && isConst i zero
  && isConst i succ
  && isConst i val
isIConst i (Vec size elem) = isConst i size && isConst i elem
isIConst i (VecElim elem motive initial nil cons val)
  = isConst i elem
  && isConst i motive
  && isConst i initial
  && isConst i nil
  && isConst i cons
  && isConst i val
isIConst i (Eq ty left right) = isConst i ty && isConst i left && isConst i right
isIConst i (EqElim a b c d e f)
  = isConst i a
  && isConst i b
  && isConst i c
  && isConst i d
  && isConst i e
  && isConst i f
isIConst i (Fin n) = isConst i n
isIConst i (FinElim a b c d e)
  = isConst i a
  && isConst i b
  && isConst i c
  && isConst i d
  && isConst i e
isIConst i (PolyElim a b c)
  = isConst i a
  && isConst i b
  && isConst i c
isIConst i (Sigma f s) = isConst i f && isConst i s
isIConst i (SigElim a b c d e)
  = isConst i a
  && isConst i b
  && isConst i c
  && isConst i d
  && (isConst i e -- either e is const
    || e == Inf (Bound i)  -- or e is bound by the value we're looking at
    && isConst 0 d         -- And the eliminator does not use the value
    && isConst 1 d)        -- in which case the entire expresion is const

isIConst i (If a b c d)
  = isConst i a
  && isConst i b
  && isConst i c
  && isConst i d
isIConst i _ = True

isConst :: Int -> CTerm -> Bool
isConst i (Inf term) = isIConst i term
isConst i (Lam body) = isConst (i + 1) body
isConst i (Succ n) = isConst i n
isConst i (Nil ty) = isConst i ty
isConst i (Cons a b c d)
  = isConst i a
  && isConst i b
  && isConst i c
  && isConst i d
isConst i (Refl left right) = isConst i left && isConst i right
isConst i (FZero ty) = isConst i ty
isConst i (FSucc bound n) = isConst i bound && isConst i n
isConst i (MkPoly shapes pos) = isConst i shapes && isConst i pos
isConst i (Comma t1 t2 p1 p2)
  = isConst i t1
  && isConst i t2
  && isConst i p1
  && isConst i p2
isConst i _ = True
