{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Bool where

import Data.Coerce

class I (c :: Bool -> *) where
  fn :: [c True] -> c False

type family Inst (x :: Bool) :: *
type instance Inst True = Int
type instance Inst False = String

newtype WrapInst (x :: Bool) = WrapInst (Inst x)

gn :: [Int] -> String
gn = unlines . fmap show

instance I WrapInst where
  fn = coerce . gn . coerce


