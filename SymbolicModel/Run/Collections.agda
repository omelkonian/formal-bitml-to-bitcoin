------------------------------------------------------------------------
-- Collecting elements out of symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Closures
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.ToList
open import Prelude.Lists.Collections

open import BitML.BasicTypes

module SymbolicModel.Run.Collections (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel.Run.Base ⋯
  hiding ( _∎; begin_)

private variable X : Type

instance
  HXʳ : ⦃ ∀ {Γₜ Γₜ′} → (Γₜ —↠ₜ Γₜ′) has X ⦄ → Run has X
  HXʳ ⦃ h ⦄ .collect = collect ⦃ h ⦄ ∘ trace

-- [BUG] instantiated `advertisements ⦃ HAʳ ⦄`, to aid Agda's type inference
authorizedHonAdsʳ : Run → List Ad
authorizedHonAdsʳ = advertisements

labelsʳ : Run → Labels
labelsʳ = labels

-- ** properties
start∈allCfgsᵗ : R .start ∈ allTCfgs⁺ R
start∈allCfgsᵗ {R = record {trace = _ , Γ↞}} with Γ↞
... | _ ∎ₜ              = here refl
... | _ —→ₜ⟨ _ ⟩ _ ⊢ tr = here refl

end∈allCfgsᵗ : ∀ R → R .end ∈ allTCfgs⁺ R
end∈allCfgsᵗ = go ∘ _∙trace′
  module ⟫end∈allCfgsᵗ where
    go : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γₜ′ ∈ allStatesᵗ⁺ tr
    go (_ ∎ₜ)              = here refl
    go (_ —→ₜ⟨ _ ⟩ _ ⊢ tr) = there (go tr)

open ≡-Reasoning

allTCfgs≡ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → allTCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ allTCfgs R ∷ʳ Γₜ
allTCfgs≡  {α}{Γₜ′}{Γₜ}{R@(record {trace = _ , Γ↞})}{x} Γ← eq =
  begin
    allTCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    toList (allTCfgs⁺ $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    toList (allStatesᵗ⁺ $ Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞)
  ≡⟨ cong toList $ allStatesᵗ⁺-∷ʳ Γ↞ Γ← eq ⟩
    toList (allStatesᵗ⁺ Γ↞ ⁺∷ʳ Γₜ)
  ≡⟨⟩
    allTCfgs R ∷ʳ Γₜ
  ∎

allCfgs≡ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → allCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ allCfgs R ∷ʳ cfg Γₜ
allCfgs≡  {α}{Γₜ′}{Γₜ}{R@(record {trace = _ , Γ↞})}{x} Γ← eq =
  begin
    allCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    map cfg (allTCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (map cfg) (allTCfgs≡ {R = R} Γ← eq) ⟩
    map cfg (allTCfgs R ∷ʳ Γₜ)
  ≡⟨ L.map-++-commute cfg (allTCfgs R) [ Γₜ ] ⟩
    map cfg (allTCfgs R) ++ [ cfg Γₜ ]
  ≡⟨⟩
    allCfgs R ∷ʳ cfg Γₜ
  ∎

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
