------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------
open import Prelude.Init hiding (Σ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures

module SymbolicModel.Strategy2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run2 Participant Honest
open import SymbolicModel.Collections2 Participant Honest
-- open import SymbolicModel.Stripping2 Participant Honest
