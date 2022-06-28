------------------------------------------------------------------------
-- Collecting elements out of symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Closures
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.Collections

module SymbolicModel.Collections
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
  hiding ( _∎; begin_)

open ≡-Reasoning

private variable X : Set

instance
  HXʳ : ⦃ ∀ {Γₜ Γₜ′} → (Γₜ —↠ₜ Γₜ′) has X ⦄ → Run has X
  HXʳ ⦃ h ⦄ .collect = collect ⦃ h ⦄ ∘ trace

-- [BUG] instantiated `advertisements ⦃ HAʳ ⦄`, to aid Agda's type inference
authorizedHonAdsʳ : Run → List Advertisement
authorizedHonAdsʳ = collect

ads⦅end⦆⊆ : ∀ R → advertisements (R .end) ⊆ advertisements R
ads⦅end⦆⊆ R
  = ⊆-concat⁺
  $ L.Mem.∈-map⁺ advertisements
  $ L.Mem.∈-map⁺ cfg
  $ end∈allCfgsᵗ R

names⦅end⦆⊆ : (R : Run) → names (R .end) ⊆ names R
names⦅end⦆⊆ R = ⊆-concat⁺
              $ L.Mem.∈-map⁺ names
              $ L.Mem.∈-map⁺ cfg
              $ end∈allCfgsᵗ R

namesˡ⦅end⦆⊆ : ∀ (R : Run) → namesˡ (R .end) ⊆ namesˡ R
namesˡ⦅end⦆⊆ = mapMaybe-⊆ isInj₁ ∘ names⦅end⦆⊆

namesʳ⦅end⦆⊆ : ∀ (R : Run) → namesʳ (R .end) ⊆ namesʳ R
namesʳ⦅end⦆⊆ = mapMaybe-⊆ isInj₂ ∘ names⦅end⦆⊆

ads-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ advertisements R ++ advertisements (cfg Γₜ)
ads-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq =
  begin
    advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    concatMap authorizedHonAds (allCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (concatMap authorizedHonAds) (allCfgs≡ {R = R} Γ← eq) ⟩
    concatMap authorizedHonAds (allCfgs R ∷ʳ cfg Γₜ)
  ≡⟨ concatMap-++ authorizedHonAds (allCfgs R) [ cfg Γₜ ] ⟩
    concatMap authorizedHonAds (allCfgs R) ++ concatMap authorizedHonAds [ cfg Γₜ ]
  ≡⟨⟩
    advertisements R ++ concatMap authorizedHonAds [ cfg Γₜ ]
  ≡⟨ cong (advertisements R ++_) (L.++-identityʳ _) ⟩
    advertisements R ++ authorizedHonAds (cfg Γₜ)
  ∎

names-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → names (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ names R ++ names Γₜ
names-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq =
  begin
    names (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    concatMap collect (allCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (concatMap collect) (allCfgs≡ {R = R} Γ← eq) ⟩
    concatMap collect (allCfgs R ∷ʳ cfg Γₜ)
  ≡⟨ concatMap-++ collect (allCfgs R) [ cfg Γₜ ] ⟩
    concatMap collect (allCfgs R) ++ concatMap collect [ cfg Γₜ ]
  ≡⟨⟩
    names R ++ concatMap collect [ cfg Γₜ ]
  ≡⟨ cong (names R ++_) (L.++-identityʳ _) ⟩
    names R ++ collect (cfg Γₜ)
  ∎

namesˡ-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → namesˡ (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ namesˡ R ++ namesˡ Γₜ
namesˡ-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq
  rewrite names-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq = mapMaybe-++ isInj₁ (names R) (names Γₜ)

namesʳ-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → namesʳ (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ namesʳ R ++ namesʳ Γₜ
namesʳ-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq
  rewrite names-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq = mapMaybe-++ isInj₂ (names R) (names Γₜ)

names-∎ : ∀ {init : Initial Γₜ₀}
  → names (Γₜ₀ ∎⊣ init)
  ≡ names Γₜ₀
names-∎ = L.++-identityʳ _

namesˡ-∎ : ∀ {init : Initial Γₜ₀}
  → namesˡ (Γₜ₀ ∎⊣ init)
  ≡ namesˡ Γₜ₀
namesˡ-∎ {Γ₀}{init} = cong filter₁ $ names-∎ {Γ₀}{init}

namesʳ-∎ : ∀ {init : Initial Γₜ₀}
  → namesʳ (Γₜ₀ ∎⊣ init)
  ≡ namesʳ Γₜ₀
namesʳ-∎ {Γ₀}{init} = cong filter₂ $ names-∎ {Γ₀}{init}

ads-∎ : ∀ {init : Initial Γₜ₀}
  → advertisements (Γₜ₀ ∎⊣ init)
  ≡ advertisements Γₜ₀
ads-∎ = L.++-identityʳ _

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
