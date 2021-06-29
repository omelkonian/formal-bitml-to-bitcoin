open import Prelude.Init
open import Prelude.DecEq

module SymbolicModel2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run2 Participant Honest public
open import SymbolicModel.Collections2 Participant Honest public
-- open import SymbolicModel.Stripping Participant Honest public
open import SymbolicModel.Helpers2 Participant Honest public
