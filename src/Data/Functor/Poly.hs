{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE StandaloneKindSignatures #-} GHC 8.10 only

module Data.Functor.Poly where

import Data.Bifunctor
import Data.Kind

type Container = (Type, Type)

-- type Prod :: Container -> Container -> Container
type family Prod (c1 :: Container) (c2 :: Container) :: Container where
  Prod '(a, b) '(x, y) = '((a, x), (b, y))

-- type Sum :: Container -> Container -> Container
type family Sum (c1 :: Container) (c2 :: Container) :: Container where
  Sum '(a, b) '(x, y) = '(Either a x, Either b y)

-- x       y
--     ->
-- s       r
-- | Morphism of containers
data Morphism :: Container -> Container -> Type where
  Lens :: forall (x :: Type) (s :: Type) (y :: Type) (r :: Type).
          (x -> y) -> (x -> r -> s) -> Morphism '(x, s) '(y, r)

-- | Parallel composition of lenses
parallel :: forall (c1 :: Container) (c2 :: Container) (c3 :: Container) (c4 :: Container).
            Morphism c1 c2 -> Morphism c3 c4 -> Morphism (Prod c1 c3) (Prod c2 c4)
parallel (Lens fw1 bw1) (Lens fw2 bw2) = Lens
  (bimap fw1 fw2)
  (\(a, b) -> bimap (bw1 a) (bw2 b))

type UnitContainer = '((),())

functionAsDynamics :: (a -> b) -> Morphism '(a, b) UnitContainer
functionAsDynamics fn = Lens (const ()) (\x -> const (fn x))
