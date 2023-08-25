open import Prelude.Init

open import SecureCompilation.ModuleParameters using (⋯)

module Coherence.Properties (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′
open import ComputationalModel ⋯′ finPart keypairs as C
open import Coherence.Helpers ⋯
open import Coherence.Hypotheses ⋯
open import Coherence.Relation ⋯
open import SecureCompilation.ComputationalContracts ⋯′

postulate instance
  -- type inequalities
  ℤ×ℤ≢Ad    : (ℤ × ℤ)        ≢′ Advertisementᶜ
  ∃Tx≢Ad    : ∃Tx            ≢′ Advertisementᶜ
  Ad≢Tx     : Advertisementᶜ ≢′ Tx i o
  String≢Tx : String         ≢′ Tx i o
  Tx≢String : Tx i o         ≢′ String

module _ {Rˢ Γₜ Rᶜ} {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} where

  get-λᶜ : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ → C.Label
  get-λᶜ {λᶜ = λᶜ} _ = λᶜ

  get-λᶜ-correct : (coh : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ)
                  → get-λᶜ coh ≡ λᶜ
  get-λᶜ-correct _ = refl

  module _ {A} (T : Tx i o) where abstract
    λᶜ≢encodeT : (coh : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ)
               → get-λᶜ coh ≢ A →∗∶ encode T
    λᶜ≢encodeT coh with coh
    ... | [L1] mkℍ = label≢ encode≢
    ... | [L2] mkℍ _ _ _ _ _ _ _ = label≢ (SIG≢encode {y = T})
    ... | [L3] mkℍ _ _ = label≢ (SIG≢encode {y = T})
    ... | [L4] mkℍ = λ ()
    ... | [L5] mkℍ = label≢ (SIG≢encode {y = T})
    ... | [L6] mkℍ = λ ()
    ... | [L7] mkℍ _ _ _ _ _ = label≢ encode≢
    ... | [L8] mkℍ = λ ()
    ... | [L9] mkℍ = λ ()
    ... | [L10] mkℍ (_ , _ , _) _ = label≢ (SIG≢encode {y = T})
    ... | [L11] mkℍ = λ ()
    ... | [L12] mkℍ (_ , _ , _) _ = label≢ (SIG≢encode {y = T})
    ... | [L13] mkℍ = λ ()
    ... | [L14] mkℍ (_ , _ , _) _ = label≢ (SIG≢encode {y = T})
    ... | [L15] mkℍ = λ ()
    ... | [R16⊣ _ ] mkℍ (_ , _ , _) _ = label≢ (SIG≢encode {y = T})
    ... | [R17⊣ _ ] mkℍ _ _ = λ ()
    ... | [L18]  mkℍ = λ ()

    ≁₁-encodeT : Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁ A →∗∶ encode T ⨾ Rᶜ
    ≁₁-encodeT coh = λᶜ≢encodeT coh $ get-λᶜ-correct coh
