{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Data.Machine.Moore where

import Data.Boundary

-- moore machines, you can only have one of them per state
class Moore state output input | state -> input , state -> output where
  extract :: state -> output
  update :: state -> input -> state

-- each moore machine gives rise to a morphism
mooreAsLens :: Moore st out inp => Morphism '(st, st) '(out, inp)
mooreAsLens = Lens extract update

data FibState = FibState { p0 :: Int, p1 :: Int }

instance Moore FibState Int () where
  extract (FibState p0 p1) = p1
  update (FibState p0 p1) () = FibState p1 (p0 + p1)

fibonacciMoore :: Morphism '(FibState, FibState) '(Int, ())
fibonacciMoore = mooreAsLens

type family N :: Boundary where
  N = '(Int, Int)

idNat :: Morphism N N
idNat = identity

gamma :: Morphism (Prod N N) '(Int, ())
gamma = Lens snd (\(old2, old1) () -> (old1, old2 + old1))

initZero :: Morphism UnitBoundary N
initZero = Lens (const 0) (const (const ()))

initOne :: Morphism UnitBoundary N
initOne = Lens (const 1) (const (const ()))

collapse :: Morphism UnitBoundary (Prod UnitBoundary UnitBoundary)
collapse = Lens (const ((),())) (const (const ()))

-- we want this but as a data descritpion we can render
fibSystem :: Morphism UnitBoundary '(Int, ())
fibSystem = collapse |> (initZero `parallel` initOne) |> (idNat `parallel` idNat) |> gamma
