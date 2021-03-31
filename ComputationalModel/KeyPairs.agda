open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

open import Bitcoin.Crypto

module ComputationalModel.KeyPairs
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄

  (keypairs : Participant → KeyPair × KeyPair)
  where

K : Participant → KeyPair
K = proj₁ ∘ keypairs

K̂ : Participant → KeyPair
K̂ = proj₂ ∘ keypairs

Kᵖ : Participant → ℤ
Kᵖ = pub ∘ K

Kˢ : Participant → ℤ
Kˢ = sec ∘ K

K̂ᵖ : Participant → ℤ
K̂ᵖ = pub ∘ K̂

K̂ˢ : Participant → ℤ
K̂ˢ = sec ∘ K̂
