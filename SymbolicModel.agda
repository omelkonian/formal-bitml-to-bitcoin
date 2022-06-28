open import Prelude.Init
open import Prelude.DecEq

module SymbolicModel
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest public
open import SymbolicModel.Accessors Participant Honest public
open import SymbolicModel.Collections Participant Honest public
open import SymbolicModel.Mappings Participant Honest public
open import SymbolicModel.ValuePreservation Participant Honest public
open import SymbolicModel.Helpers Participant Honest public

open import SymbolicModel.Strategy Participant Honest public
-- open import SymbolicModel.Stripping Participant Honest public
