------------------------------------------------------------------------
--
--
--
------------------------------------------------------------------------

module Agdernoon.Data.Bool where

------------------------------------------------------------------------
--

data Bool : Set where
  true  : Bool
  false : Bool

------------------------------------------------------------------------
--

not : Bool → Bool
not true  = false
not false = true
