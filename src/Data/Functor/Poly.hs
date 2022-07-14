{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE StandaloneKindSignatures #-} GHC 8.10 only

module Data.Functor.Poly where

import Data.Bifunctor
import Data.Kind
import Data.Boundary
import Data.Functor.Const

data Container :: Type where
  Cont :: (x :: Type) -> (x -> Type) -> Container

testCont :: Container
testCont = undefined -- how do I build a value of Container????

type family Shape (c :: Container) :: Type where
  Shape (Cont x _) = x

type family Positions (c :: Container) (v :: Shape c) :: Type where
  -- Shape (Cont s p) v = p v -- How do I do this???

type family FromBoundary (x :: Type) (y :: Type) :: Container where
  FromBoundary a b = Cont a (Const b)

data family Choice :: (x, y) -> Type

type family DepSum (x :: Type) (y :: Type) (f :: x -> Type) (g :: y -> Type) :: (x, y) -> Type where
  DepSum x y f g = Choice

data CMorphism :: Container -> Container -> Type where
  MkDLens :: -- (fw :: (Shape c1 -> Shape c2)) -- this name doesn't work
             ((Shape c1 -> Shape c2)) -- But this works
          -- -> ((x :: Shape c1) -> Positions c2 (fw x) -> Positions c1 x
          -- This has no chance of working because `Positions` does not work
          -> CMorphism c1 c2
