{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module Data.Boundary where

import Data.Bifunctor
import Data.Kind

type Boundary = (Type, Type)

-- type Prod :: Boundary -> Boundary -> Boundary
type family Prod (c1 :: Boundary) (c2 :: Boundary) :: Boundary where
  Prod '(a, b) '(x, y) = '((a, x), (b, y))

-- type Sum :: Boundary -> Boundary -> Boundary
type family Sum (c1 :: Boundary) (c2 :: Boundary) :: Boundary where
  Sum '(a, b) '(x, y) = '(Either a x, Either b y)

-- x       y
--     ->
-- s       r
-- | Morphism of containers
data Morphism :: Boundary -> Boundary -> Type where
  Lens :: forall (x :: Type) (s :: Type) (y :: Type) (r :: Type).
          (x -> y) -> (x -> r -> s) -> Morphism '(x, s) '(y, r)

-- | Parallel composition of lenses
parallel :: forall (c1 :: Boundary) (c2 :: Boundary) (c3 :: Boundary) (c4 :: Boundary).
            Morphism c1 c2 -> Morphism c3 c4 -> Morphism (Prod c1 c3) (Prod c2 c4)
parallel (Lens fw1 bw1) (Lens fw2 bw2) = Lens
  (bimap fw1 fw2)
  (\(a, b) -> bimap (bw1 a) (bw2 b))

type UnitBoundary = '((),())

-- ^ Functions are trivial dynamical systems
functionAsDynamics :: (a -> b) -> Morphism '(a, b) UnitBoundary
functionAsDynamics fn = Lens (const ()) (\x -> const (fn x))
