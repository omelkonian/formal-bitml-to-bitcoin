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

open import SymbolicModel.Strategy ⋯′ as S
open import ComputationalModel.Strategy ⋯′ finPart keypairs as C
open import Coherence ⋯
open import SecureCompilation.Parsing ⋯
open import SecureCompilation.Unparsing ⋯
open import SecureCompilation.StrategyTranslation ⋯

module _
  Adv (Adv∉ : Adv ∉ Hon)
  (Σˢ : S.HonestStrategies)
  (open S.AdvM Adv Adv∉ renaming (AdversaryStrategy to AdvStrategyˢ))
  (open C.AdvM Adv Adv∉ renaming (AdversaryStrategy to AdvStrategyᶜ))
  (𝕧Σˢ : ∀ {A} (A∈ : A ∈ Hon) → Valid (Σˢ A∈))
  (Σᶜₐ : AdvStrategyᶜ)
  where

  -- [T0D0] missing translation for adversarial strategy
  postulate ℵₐ : AdvStrategyᶜ → AdvStrategyˢ

  Σˢₐ : AdvStrategyˢ
  Σˢₐ = ℵₐ Σᶜₐ

  Σᶜ : C.HonestStrategies
  Σᶜ A∈ = ℵ A∈ (Σˢ A∈ , 𝕧Σˢ A∈) .proj₁

  Theorem2 : ∀ Rᶜ →
    Rᶜ ∼ᶜ Σᶜₐ , Σᶜ
    ───────────────────────────────────────────────
    ∃ λ Rˢ → (Rˢ ∼ˢ Σˢₐ , Σˢ) × (Rˢ ~ Rᶜ)

  ⦅1⦆completeness : ∀ Rᶜ → ∃ (_~ Rᶜ)
  ⦅1⦆completeness = parseRun~

  ⦅2⦆soundness : ∀ Rᶜ →
    Rᶜ ∼ᶜ Σᶜₐ , Σᶜ
    ───────────────────────
    parseRun Rᶜ ∼ˢ Σˢₐ , Σˢ
  ⦅2⦆soundness Rᶜ ∃R~ᶜ@(Rᶜ⋯ , prefix , R~ᶜ)
    -- [T0D0] overcome non-constructive formulation of the original proof
    with Rˢ , Rˢ~Rᶜ ← parseRun~ Rᶜ
    = R~ˢ
    where
      R~ˢ : Rˢ ∼ˢ Σˢₐ , Σˢ
      R~ˢ with ⟫ R~ᶜ
      -- T0D0: induction in tandem with `parseRun~` needed here
      ... | ⟫ base {R} cinit = {!?!}
      ... | ⟫ step {R} h1 h2 h3 = {!?!}
      ... | ⟫ oracle-adv {R}{m}{hm} h1 h2 h3 h4 = {!!}
      ... | ⟫ oracle-hon {R}{A}{A∈}{m}{hm} h1 h2 h3 = {!!}

  Theorem2 Rᶜ R~ᶜ =
    let Rˢ , Rˢ~Rᶜ = ⦅1⦆completeness Rᶜ
    in Rˢ , ⦅2⦆soundness Rᶜ R~ᶜ , Rˢ~Rᶜ
