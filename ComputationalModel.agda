open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

import Bitcoin.Crypto as BTC

module ComputationalModel
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → BTC.KeyPair × BTC.KeyPair)

  where

-- re-export all Bitcoin definitions
open import Bitcoin public

open import ComputationalModel.KeyPairs Participant keypairs public
open import ComputationalModel.Strategy Participant Honest finPart keypairs public
open import ComputationalModel.Lemmas Participant Honest finPart keypairs public
