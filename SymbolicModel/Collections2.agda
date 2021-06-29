-- {-# OPTIONS --allow-unsolved-metas #-}
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
open import Prelude.Setoid

module SymbolicModel.Collections2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run2 Participant Honest

instance
  HAʳ : Run has Advertisement
  HAʳ .collect = concatMap authorizedHonAds ∘ allCfgs

  HNʳ : Run has Name
  -- HNʳ .collect = mkCollectʳ
  HNʳ .collect = collect ∘ end

  HSʳ : Run has Secret
  HSʳ .collect = filter₂ ∘ collect {B = Name}

  HL↠ : (Γ —[ αs ]↠ Γ′) has Label
  HL↠ {αs = αs} .collect _ = αs

  HL↠′ : (Γ —↠ Γ′) has Label
  HL↠′ .collect = proj₁

  HL↠ₜ : (Γₜ —[ αs ]↠ₜ Γₜ′) has Label
  HL↠ₜ {αs = αs} .collect _ = αs

  HL↠ₜ′ : (Γₜ —↠ₜ Γₜ′) has Label
  HL↠ₜ′ .collect = proj₁

  HLʳ : Run has Label
  HLʳ .collect = collect ∘ trace

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

ads⦅end⦆⊆ : advertisements (R .end) ⊆ advertisements R
ads⦅end⦆⊆ {R = R}
  = ⊆-concatMap⁺
  $ L.Mem.∈-map⁺ advertisements
  $ L.Mem.∈-map⁺ cfg
  $ end∈allCfgsᵗ {R}

ads-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ advertisements R ++ advertisements (cfg Γₜ)
ads-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq =
  begin≡
    advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    concatMap authorizedHonAds (allCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (concatMap authorizedHonAds) (allCfgs≡ {R = R} Γ← eq) ⟩
    concatMap authorizedHonAds (allCfgs R ∷ʳ cfg Γₜ)
  ≡⟨ concatMap-++ {xs = allCfgs R} {ys = [ cfg Γₜ ]} {f = authorizedHonAds} ⟩
    concatMap authorizedHonAds (allCfgs R) ++ concatMap authorizedHonAds [ cfg Γₜ ]
  ≡⟨⟩
    advertisements R ++ concatMap authorizedHonAds [ cfg Γₜ ]
  ≡⟨ cong (advertisements R ++_) (L.++-identityʳ _) ⟩
    advertisements R ++ authorizedHonAds (cfg Γₜ)
  ∎≡
  where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

ads∈-⊎ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → ad ∈ advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  → ad ∈ advertisements R
  ⊎ ad ∈ advertisements Γₜ
ads∈-⊎ {α}{Γₜ′}{Γₜ}{R}{ad}{x} Γ← eq ad∈
  rewrite ads-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq
  with L.Mem.∈-++⁻ (advertisements R) {advertisements Γₜ} ad∈
... | inj₁ ad∈R  = inj₁ ad∈R
... | inj₂ ad∈Γ′ = inj₂ ad∈Γ′
