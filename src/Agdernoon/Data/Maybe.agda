------------------------------------------------------------------------
-- The Agdernoon library
--
-- The Maybe type
------------------------------------------------------------------------

module Agdernoon.Data.Maybe where

------------------------------------------------------------------------
--

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A
