------------------------------------------------------------------------
-- Symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq

module SymbolicModel.Run
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

-- re-export all BitML definitions
open import BitML Participant Honest public
  hiding (∣_∣; `; _∙)
open import SymbolicModel.Run.Base Participant Honest public
open import SymbolicModel.Run.Properties Participant Honest public

open import SymbolicModel.Run.Example
