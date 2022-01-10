open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

open import Bitcoin.Crypto using (KeyPair)

module ComputationalModel
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  where

-- re-export all Bitcoin definitions
open import Bitcoin public
  hiding (KeyPair) -- used in the module parameters, cannot re-export

open import ComputationalModel.KeyPairs Participant keypairs public
open import ComputationalModel.Strategy Participant Honest finPart keypairs public
open import ComputationalModel.Lemmas Participant Honest finPart keypairs public
