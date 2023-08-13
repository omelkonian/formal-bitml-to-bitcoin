open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

import Bitcoin.Crypto as BTC
open import BitML.BasicTypes using (⋯)

module ComputationalModel
  (⋯ : ⋯) (let open ⋯ ⋯)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → BTC.KeyPair × BTC.KeyPair)

  where

-- re-export all Bitcoin definitions
open import Bitcoin public

open import ComputationalModel.Serialization public
open import ComputationalModel.KeyPairs Participant keypairs public
open import ComputationalModel.Strategy ⋯ finPart keypairs public
open import ComputationalModel.Lemmas ⋯ finPart keypairs public
