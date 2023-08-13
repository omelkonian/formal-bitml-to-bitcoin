open import Prelude.Init
open import Bitcoin

module ComputationalModel.KeyPairs
  (Participant : Set)
  (keypairs : Participant → KeyPair × KeyPair)
  where

K : Participant → KeyPair
K = proj₁ ∘ keypairs

K̂ : Participant → KeyPair
K̂ = proj₂ ∘ keypairs

Kᵖ : Participant → HashId
Kᵖ = pub ∘ K

Kˢ : Participant → HashId
Kˢ = sec ∘ K

K̂ᵖ : Participant → HashId
K̂ᵖ = pub ∘ K̂

K̂ˢ : Participant → HashId
K̂ˢ = sec ∘ K̂
