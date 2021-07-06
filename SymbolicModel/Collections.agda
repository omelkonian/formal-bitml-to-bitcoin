------------------------------------------------------------------------
-- Collecting elements out of symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces
open import Prelude.Setoid

open import Bitcoin.Crypto
open import Bitcoin.Tx

module SymbolicModel.Collections
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest

private variable X : Set

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

labels : ⦃ X has Label ⦄ → X → Labels
labels = collect

-- [BUG] instantiated `advertisements ⦃ HAʳ ⦄`, to aid Agda's type inference
authorizedHonAdsʳ : Run → List Advertisement
authorizedHonAdsʳ = collect

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
  ≡⟨ concatMap-++ authorizedHonAds (allCfgs R) [ cfg Γₜ ] ⟩
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

-- Useful type aliases for maps over specific sets.
Txout : ⦃ X has Name ⦄ → Pred₀ X
Txout x = namesʳ x ↦ TxInput′

Sechash : ⦃ X has Name ⦄ → Pred₀ X
Sechash x = namesˡ x ↦ ℤ

𝕂 : Pred₀ Precondition
𝕂 g = nub-participants g ↦ KeyPair

𝕂²′ : Pred₀ Advertisement
𝕂²′ (⟨ g ⟩ c) = subtermsᶜ′ c ↦ nub-participants g ↦ KeyPair

𝕂² : ⦃ X has Advertisement ⦄ → Pred₀ X
𝕂² x = advertisements x ↦′ 𝕂²′

-- [BUG] somehow if we didn't package this constructor arguments in ℝ, we get unification/panic errors!
-- (issue appear at the usage site)
-- ℝ = ∃[ R ] (Txout R × Sechash R × 𝕂² R)
record ℝ (R : Run) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txout′   : Txout R
    sechash′ : Sechash R
    κ′       : 𝕂² R

Txout≈ : _≈_ ⇒² _→⦅ Txout ⦆_
Txout≈ {Γ}{Γ′} = permute-↦ {P = const TxInput′} ∘ ≈⇒namesʳ↭ {Γ}{Γ′}

Sechash≈ : _≈_ ⇒² _→⦅ Sechash ⦆_
Sechash≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒namesˡ↭ {Γ}{Γ′}

𝕂²≈ : _≈_ ⇒² _→⦅ 𝕂² ⦆_
𝕂²≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒ads↭ {Γ}{Γ′}


lift_—⟨_⟩—_⊣_ : ∀ {Z A B : Set} {Z′ : Set} {P : Pred₀ Z′}
  → ⦃ _ : A has Z ⦄ → ⦃ _ : B has Z ⦄
  → (a : A) (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′) (b : B)
  → b ≡⦅ f ⦆ a
    --————————————————————————————————————————————————————
  → a →⦅ (λ x → f x ↦′ P) ⦆ b
(lift _ —⟨ _ ⟩— _ ⊣ eq) m rewrite eq = m
