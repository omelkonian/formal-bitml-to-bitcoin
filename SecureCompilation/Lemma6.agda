{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership

open import Bitcoin

module SecureCompilation.Lemma6
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
open import SecureCompilation.Coherence Participant Honest finPart keypairs η

lemma6 :
    (R~ : Rˢ ~ Rᶜ)
  → (⟨ c , v ⟩at x ∈ᶜ Rˢ .end .cfg)
    --——————————————————————————————
  → (∃ λ ttx →
        (ttx ∈ 𝔹 Rᶜ)
      × let
          tx = ttx .transaction
          os = tx .proj₂ .proj₂ . outputs
        in ∃ λ o
         → ∃ λ (o∈ : o V.Mem.∈ os)
         → (V.lookup os (V.Any.index o∈)) .proj₂ .value ≡ v)
         -- × let open ℝ (R~ .proj₁) in
         --   tx ∈ᵗˣ bitml-compiler {ad = ⟨G⟩C? (seek ancestor)} vad? sechash txout K̂? κ
lemma6 (𝕣 , base init₁ R≈ cinit x x₁ x₂) c∈ = {!!}
lemma6 (𝕣 , step₁ R~ x) c∈ = {!x!}
lemma6 (𝕣 , step₂ R~ ([1] x)) c∈ = {!!}
lemma6 (𝕣 , step₂ R~ ([2] x)) c∈ = {!!}
lemma6 (𝕣 , step₂ R~ ([3] x)) c∈ = {!!}
