------------------------------------------------------------------------
-- The Agdernoon library
--
--
------------------------------------------------------------------------

module Agdernoon.Data.List.Functor where

open import Agdernoon.Category.Functor
open import Agdernoon.Data.List

------------------------------------------------------------------------
--

rawFunctor : RawFunctor List
rawFunctor = record { fmap = map }
