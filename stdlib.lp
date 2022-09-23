
let fstTy = (forall (a :: Type) (b :: a -> Type). Sigma a b -> a) :: Type
let fst = (\ty sy -> sigElim ty sy (\x -> ty) (\f s -> f) ) :: fstTy

let snd =
  (\ty sy -> sigElim ty sy (\x -> sy (fst ty sy x)) (\f s -> s))
  :: forall (a :: Type) (b :: a -> Type) (s :: Sigma a b). (b (fst a b s))

let const = (\t1 t2 a b -> a) :: forall (t1 :: Type) (t2 :: Type). t1 -> t2 -> t1

let poly1 = MkPoly Nat Fin :: Poly
let poly2 = MkPoly Nat (Vec Nat) :: Poly

let Pair = (\x y -> Sigma x (\_ -> y)) :: forall (x :: Type) (y :: Type). Type
let MkPair = (\t1 t2 x y -> MkSigma t1 (\x -> t2) x y) :: forall (x :: Type) (y :: Type) . x -> y -> Pair x y

let Either = (\x y -> Sigma Bool (if (\_ -> Type) x y)) :: forall (x :: Type) (y :: Type) . Type

let Right = (\l r -> MkSigma Bool (if (\_ -> Type) l r) False)
  :: (forall (x :: Type) (y :: Type) . y -> Either x y)

let Left = (\l r -> MkSigma Bool (if (\_ -> Type) l r) True)
  :: (forall (x :: Type) (y :: Type) . x -> Either x y)

let b_type = (\x y -> if (\_ -> Type) x y) :: Type -> Type -> Bool -> Type

let eitherElim = (\x y m l r ->
  sigElim Bool
          (b_type x y)
          m
          (if (\b -> forall (v :: b_type x y b). m (MkSigma Bool (b_type x y) b v)) l r)
  )
  :: forall (x :: Type) (y :: Type)
            (m :: Either x y -> Type)
            (l :: forall (v :: x). m (Left x y v))
            (r :: forall (v :: y). m (Right x y v))
            (e :: Either x y ) .
            m e

let parallel = (\p1 p2 ->
   polyElim (\_ -> Poly)
            (\shp1 pos1 -> polyElim
              (\_ -> Poly)
              (\shp2 pos2 ->
                MkPoly (Pair shp1 shp2)
                       (sigElim shp1
                                (\_ -> shp2)
                                (\_ -> Type)
                                (\p1 p2 -> Pair (pos1 p1) (pos2 p2))))
              p2)
            p1) :: Poly -> Poly -> Poly

let multiplication = (\p1 p2 ->
   polyElim (\_ -> Poly)
            (\shp1 pos1 -> polyElim
              (\_ -> Poly)
              (\shp2 pos2 ->
                MkPoly (Pair shp1 shp2)
                       (sigElim shp1
                                (\_ -> shp2)
                                (\_ -> Type)
                                (\p1 p2 -> Either (pos1 p1) (pos2 p2))))
              p2)
            p1) :: Poly -> Poly -> Poly
let choice = (\p1 p2 ->
   polyElim (\_ -> Poly)
            (\shp1 pos1 -> polyElim
              (\_ -> Poly)
              (\shp2 pos2 ->
                MkPoly (Either shp1 shp2)
                       (eitherElim shp1 shp2
                          (\e -> Type)
                          pos1
                          pos2))
              p2)
            p1) :: Poly -> Poly -> Poly

