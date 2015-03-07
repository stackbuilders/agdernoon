------------------------------------------------------------------------
-- The Agdernoon library
--
-- Lists
------------------------------------------------------------------------

module Agdernoon.Data.List where

import Data.List

infixr 5 _∷_

------------------------------------------------------------------------
--

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
