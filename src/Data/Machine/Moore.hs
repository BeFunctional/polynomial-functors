{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DataKinds #-}

module Data.Machine.Moore where

import Data.Functor.Poly

-- moore machines, you can only have one of them per state
class Moore state output input | state -> input , state -> output where
  extract :: state -> output
  update :: state -> input -> update

-- each moore machine gives rise to a morphism
mooreAsLens :: Moore st out inp => Morphism '(st, st) '(out, inp)
mooreAsLens = Lens extract update

