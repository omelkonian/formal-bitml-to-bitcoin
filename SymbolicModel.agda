open import Prelude.Init
open import Prelude.DecEq

module SymbolicModel
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest public
open import SymbolicModel.Collections Participant Honest public
open import SymbolicModel.Stripping Participant Honest public
