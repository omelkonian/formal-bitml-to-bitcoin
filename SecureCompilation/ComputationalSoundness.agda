{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open L.Mem
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.InferenceRules
open import Prelude.Validity
open import Prelude.General

open import Bitcoin
open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.ComputationalSoundness (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
open import ComputationalModel ⋯′ finPart keypairs as C
open import Coherence ⋯
open import SecureCompilation.Parsing ⋯
open import SecureCompilation.Backtranslation ⋯

module _ Adv (Adv∉ : Adv ∉ Hon) where
  open S.AdvM Adv Adv∉ renaming (_-conforms-to-_ to _~ˢ_; AdversaryStrategy to AdvStrategyˢ)
  open C.AdvM Adv Adv∉ renaming (_-conforms-to-_ to _~ᶜ_; AdversaryStrategy to AdvStrategyᶜ)

  module _ (Σˢ : S.HonestStrategies)
           (𝕧Σˢ : ∀ {A} (A∈ : A ∈ Hon) → Valid (Σˢ A∈))
           (Σᶜₐ : AdvStrategyᶜ) where

    -- [T0D0] missing translation for adversarial strategy
    postulate ℵₐ : AdvStrategyᶜ → AdvStrategyˢ

    Σˢₐ : AdvStrategyˢ
    Σˢₐ = ℵₐ Σᶜₐ

    Σᶜ : C.HonestStrategies
    Σᶜ A∈ = ℵ A∈ (Σˢ A∈ , 𝕧Σˢ A∈) .proj₁

    -- [T0D0] overcome non-constructive formulation of the original proof
    soundness :

        Rᶜ ~ᶜ Σᶜₐ , Σᶜ
        ────────────────────────────────────────────────────
        ∃ λ (Rˢ : S.Run) → (Rˢ ~ˢ Σˢₐ , Σˢ) × (Rˢ ~ Rᶜ)

    soundness {Rᶜ} ∃R~ᶜ@(Rᶜ⋯ , prefix , R~ᶜ)
      with Rˢ , Rˢ~Rᶜ ← parseRun Rᶜ
      = Rˢ , R~ˢ , Rˢ~Rᶜ
      where
        R~ˢ : Rˢ ~ˢ Σˢₐ , Σˢ
        R~ˢ with ⟫ R~ᶜ
        -- T0D0: induction in tandem with `parseRun` needed here
        ... | ⟫ base {R} cinit = {!base ?!}
        ... | ⟫ step {R} h1 h2 h3 = {!step ? ?!}
        ... | ⟫ oracle-adv {R}{m}{hm} h1 h2 h3 h4 = {!step ?!}
        ... | ⟫ oracle-hon {R}{A}{A∈}{m}{hm} h1 h2 h3 = {!!}
