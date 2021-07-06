------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------
open import Prelude.Init hiding (Σ)
open import Prelude.DecEq

module SymbolicModel.Strategy
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
open import SymbolicModel.Collections Participant Honest
-- open import SymbolicModel.Stripping Participant Honest
