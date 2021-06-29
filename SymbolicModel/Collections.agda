------------------------------------------------------------------------
-- Collecting elements out of symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init hiding (Σ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces

module SymbolicModel.Collections
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest

-- mkCollectʳ : ∀ {X : Set} ⦃ _ : TimedConfiguration has X ⦄ → Run has X
-- mkCollectʳ ⦃ ht ⦄ .collect r with r
-- ... | Γₜ ∙         = collect ⦃ ht ⦄ Γₜ
-- ... | Γₜ ∷⟦ _ ⟧ r′ = collect ⦃ ht ⦄ Γₜ ++ collect ⦃ mkCollectʳ ⦃ ht ⦄ ⦄ r′

instance
  -- Hᵗᶜᶠ⇒Hʳ : ∀ {X : Set} ⦃ _ : TimedConfiguration has X ⦄ → Run has X
  -- -- Hᵗᶜᶠ⇒Hʳ ⦃ ht ⦄ = mkCollectʳ ⦃ ht ⦄
  -- Hᵗᶜᶠ⇒Hʳ ⦃ ht ⦄ .collect = collect ⦃ ht ⦄ ∘ lastCfgᵗ

  HAʳ : Run has Advertisement
  -- HAʳ .collect = mkCollectʳ
  -- HAʳ .collect = authorizedHonAds ∘ cfg ∘ lastCfgᵗ
  HAʳ .collect = concatMap authorizedHonAds ∘ allCfgs

  HNʳ : Run has Name
  -- HNʳ .collect = mkCollectʳ
  HNʳ .collect = collect ∘ lastCfgᵗ

  HSʳ : Run has Secret
  HSʳ .collect = filter₂ ∘ collect {B = Name}

  HLʳ : Run has Label
  HLʳ .collect (_ ∙)        = []
  HLʳ .collect (_ ∷⟦ α ⟧ R) = α ∷ collect R

labels : ∀ {X : Set} → ⦃ _ :  X has Label ⦄ → X → Labels
labels = collect

-- [BUG] instantiated `advertisements ⦃ HAʳ ⦄`, to aid Agda's type inference
authorizedHonAdsʳ : Run → List Advertisement
authorizedHonAdsʳ = concatMap authorizedHonAds ∘ allCfgs

-- ** ancestor advertisement of an active contract

Ancestor : Run → ActiveContract → Advertisement → Set
Ancestor R (c , v , x) ad
  = (c ⊆ subtermsᶜ′ (C ad))
  × (ad ∈ advertisements R)
  × Any ((` ad) ∈ᶜ_) Rᶜ
  × Any (⟨ c , v ⟩at x ∈ᶜ_) Rᶜ
  where Rᶜ = allCfgs R

Ancestor⇒∈ : Ancestor R (c , v , x) ad → c ⊆ subtermsᶜ′ (C ad)
Ancestor⇒∈ = proj₁

Ancestor→𝕂 : Ancestor R (c , v , x) ad → ad ∈ advertisements R
Ancestor→𝕂 = proj₁ ∘ proj₂

-- T0D0: replace with SymbolicModel.Ancestor, with proper provenance
