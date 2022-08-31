{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open L.Mem
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.InferenceRules
open import Prelude.Validity

open import Bitcoin

module SecureCompilation.ComputationalSoundness
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
open import ComputationalModel Participant Honest finPart keypairs as C
open import SecureCompilation.Coherence Participant Honest finPart keypairs η as SC
open import SecureCompilation.Backtranslation Participant Honest finPart keypairs η

module _ Adv (Adv∉ : Adv ∉ S.Hon) where
  open S.AdvM Adv Adv∉ renaming (_-conforms-to-_ to _~ˢ_; AdversaryStrategy to AdvStrategyˢ)
  open C.AdvM Adv Adv∉ renaming (_-conforms-to-_ to _~ᶜ_; AdversaryStrategy to AdvStrategyᶜ)

  module _ (Σˢ : S.HonestStrategies)
           (𝕧Σˢ : ∀ {A} (A∈ : A ∈ S.Hon) → Valid (Σˢ A∈))
           (Σᶜₐ : AdvStrategyᶜ) where

    -- [T0D0] missing translation for adversarial strategy
    Σˢₐ : AdvStrategyˢ
    Σˢₐ = {!!}

    Σᶜ : C.HonestStrategies
    Σᶜ A∈ = ℵ A∈ (Σˢ A∈ , 𝕧Σˢ A∈) .proj₁

    soundness :

        Rᶜ ~ᶜ Σᶜₐ , Σᶜ
        ────────────────────────────────────────────────────
        ∃ λ (Rˢ : S.Run) → (Rˢ ~ˢ Σˢₐ , Σˢ) × (Rˢ ~ Rᶜ)

    soundness = {!!}
    -- [T0D0] overcome non-constructive formulation of proof for `soundness`
