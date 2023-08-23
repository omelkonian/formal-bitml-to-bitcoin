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

module _ {Rˢ Γₜ Rᶜ} {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} where

  get-λᶜ : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ → C.Label
  get-λᶜ {λᶜ = λᶜ} _ = λᶜ

  get-λᶜ-correct : (coh : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ)
                  → get-λᶜ coh ≡ λᶜ
  get-λᶜ-correct _ = refl

  module _ {A} (T : Tx i o) where abstract
    λᶜ≢encodeT : (coh : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ)
               → get-λᶜ coh ≢ A →∗∶ encode T
    λᶜ≢encodeT ([L1] mkℍ) = label≢ encode≢
    λᶜ≢encodeT ([L2] mkℍ _ _ _ _ _ _ _) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([L3] mkℍ _ _) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([L4] mkℍ) = λ ()
    λᶜ≢encodeT ([L5] mkℍ) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([L6] mkℍ) = λ ()
    λᶜ≢encodeT ([L7] mkℍ _ _ _ _ _) = label≢ encode≢
    λᶜ≢encodeT ([L8] mkℍ) = λ ()
    λᶜ≢encodeT ([L9] mkℍ) = λ ()
    λᶜ≢encodeT ([L10] mkℍ (_ , _ , _) _) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([L11] mkℍ) = λ ()
    λᶜ≢encodeT ([L12] mkℍ (_ , _ , _) _) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([L13] mkℍ) = λ ()
    λᶜ≢encodeT ([L14] mkℍ (_ , _ , _) _) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([L15] mkℍ) = λ ()
    λᶜ≢encodeT ([R16⊣ ¬coh ] mkℍ (_ , _ , _) _) = label≢ (SIG≢encode {y = T})
    λᶜ≢encodeT ([R17⊣ ¬coh ] mkℍ _ _) = λ ()
    λᶜ≢encodeT ([L18] mkℍ) = λ ()

    ≁₁-encodeT : Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁ A →∗∶ encode T ⨾ Rᶜ
    ≁₁-encodeT coh = λᶜ≢encodeT coh $ get-λᶜ-correct coh
