open import Prelude.Init
open import Prelude.DecEq

module SymbolicModel.Mappings
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Mappings.Base Participant Honest public
open import SymbolicModel.Mappings.Properties Participant Honest public
