open import Prelude.Init
open L.Mem
open L.Perm using (∈-resp-↭)
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Collections
open import Prelude.Lists.Mappings
open import Prelude.Lists.Permutations
open import Prelude.Lists.MapMaybe

open import Bitcoin.Crypto
open import Bitcoin.Tx
open import ComputationalModel.Accessors

module SymbolicModel.ValuePreservation
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest as S
  hiding (_∎; begin_)
open import SymbolicModel.Accessors Participant Honest
open import SymbolicModel.Collections Participant Honest
open import SymbolicModel.Mappings Participant Honest

open ≡-Reasoning

ValuePreserving : Pred₀ (Txout Γ)
ValuePreserving {Γ} txout = ∀ {x} (x∈ : x ∈ ids Γ) → txout x∈ ∙value ≡ (Γ , x∈) ∙value

pv-cons-↦ : ∀ {txoutΓ : Txout Γ} {y : Id} {tx : TxInput′} →
  ∙ tx ∙value ≡ v
  ∙ ValuePreserving {Γ} txoutΓ
    ──────────────────────────────────────
    ValuePreserving {⟨ c , v ⟩at y ∣ Γ} (cons-↦ y tx txoutΓ)
pv-cons-↦ tx≡ pv x∈ with x∈
... | here refl = tx≡
... | there x∈  = pv x∈

ValuePreserving⊆ : Pred₀ (Γ ⊆⦅ ids ⦆ Γ′)
ValuePreserving⊆ {Γ}{Γ′} p =
  ∀ {x} (x∈ : x ∈ ids Γ) → (Γ , x∈) ∙value ≡ (Γ′ , p x∈) ∙value

pv-weaken-↦ : ∀ (txout : Txout Γ) (p : Γ′ ⊆⦅ ids ⦆ Γ) →
  ∙ ValuePreserving⊆ {Γ′}{Γ} p
  ∙ ValuePreserving {Γ} txout
    ─────────────────────────────────────
    ValuePreserving {Γ′} (weaken-↦ txout p)
pv-weaken-↦ {Γ}{Γ′} txout p pv⊆ pv x∈ =
  begin
    txout (p x∈) ∙value
  ≡⟨ pv _ ⟩
    (Γ , p x∈) ∙value
  ≡˘⟨ pv⊆ _ ⟩
    (Γ′ , x∈) ∙value
  ∎

-- weaken-subst-↦ : ∀ {xs ys : Ids} (txout : Txout Γ) (ids≡ : ids Γ ≡ xs ++ ys) →
--   ∀ {x} (x∈ : x ∈ ys)
--     → weaken-↦ (txout :~ ids≡ ⟪ _↦ TxInput′ ⟫) (∈-++⁺ʳ _) x∈
--     ≡ weaken-↦ txout (⟪ ys ⊆_ ⟫ ids≡ ~: ∈-++⁺ʳ _) x∈
-- weaken-subst-↦ txout ids≡ x∈ rewrite ids≡ = {!refl!}

ValuePreserving↭ : Pred₀ (Γ ↭⦅ ids ⦆ Γ′)
ValuePreserving↭ {Γ}{Γ′} p =
  ∀ {x} (x∈ : x ∈ ids Γ) → (Γ , x∈) ∙value ≡ (Γ′ , ∈-resp-↭ p x∈) ∙value

pv-permute-↦ : ∀ (txout : Txout Γ) (p : Γ ↭⦅ ids ⦆ Γ′) →
  ∙ ValuePreserving↭ {Γ}{Γ′} p
  ∙ ValuePreserving {Γ} txout
    ────────────────────────────────────────
    ValuePreserving {Γ′} (permute-↦ p txout)
pv-permute-↦ {Γ}{Γ′} txout p pv↭ pv {x} x∈ =
  begin
    txout (∈-resp-↭ (↭-sym p) x∈) ∙value
  ≡⟨ pv _ ⟩
    (Γ , ∈-resp-↭ (↭-sym p) x∈) ∙value
  ≡⟨ pv↭ _ ⟩
    (Γ′ , ∈-resp-↭ p (∈-resp-↭ (↭-sym p) x∈)) ∙value
  ≡⟨ cong (λ (◆ : x ∈ ids Γ′) → (Γ′ , ◆) ∙value)
        $ ∈-resp-↭˘∘∈-resp-↭ p x∈ ⟩
    (Γ′ , x∈) ∙value
  ∎

ValuePreserving-Txout≈ : (Γ≈ : Γ ≈ Γ′) (txout : Txout Γ) →
  ValuePreserving {Γ} txout
  ───────────────────────────────────────────────
  ValuePreserving {Γ′} (Txout≈ {Γ}{Γ′} Γ≈ txout)
ValuePreserving-Txout≈ {Γ}{Γ′} Γ≈ txout pv x∈ =
  begin
    Txout≈ {Γ}{Γ′} Γ≈ txout x∈ ∙value
  ≡⟨⟩
    permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout x∈ ∙value
  ≡⟨ pv-permute-↦ {Γ}{Γ′} txout (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) pv↭ pv x∈ ⟩
    (Γ′ , x∈) ∙value
  ∎ where
    pv↭ : ValuePreserving↭ {Γ}{Γ′} (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈)
    pv↭ {x} x∈ =
      begin
        (Γ , x∈) ∙value
      ≡˘⟨ ∈namesʳ-resp-≈∙value {Γ}{Γ′} Γ≈ x∈ ⟩
        (Γ′ , ∈namesʳ-resp-≈ x {Γ}{Γ′} Γ≈ x∈) ∙value
      ≡⟨⟩
        (Γ′ , ∈-resp-↭ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) x∈) ∙value
      ∎

ValuePreserving↝ : Pred₀ (Γ →⦅ Txout ⦆ Γ′)
ValuePreserving↝ {Γ}{Γ′} txout↝ = ∀ (txoutΓ : Txout Γ) →
  ValuePreserving {Γ} txoutΓ
  ────────────────────────────────────
  ValuePreserving {Γ′} (txout↝ txoutΓ)

ValuePreservingʳ : Pred₀ (ℝ R)
ValuePreservingʳ 𝕣 = ValuePreserving {𝕣 ∙cfg} (𝕣 ∙txoutEnd_)

-- ValuePreservingʳ : Pred₀ (Txout R)
-- ValuePreservingʳ {R} txout = ∀ {x} (x∈ : x ∈ ids R) → txout x∈ ∙value ≡ (R , x∈) ∙value

-- ValuePreservingʳ-∷ : ∀ (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
--                        (txoutΓ : Txout Γ′) (txoutR : Txout R) →
--   ∙ ValuePreserving txoutΓ
--   ∙ ValuePreservingʳ txoutR
--     ─────────────────────────────────────────────
--     ValuePreservingʳ (txout∷ Γ→ eq txoutΓ txoutR)
-- ValuePreservingʳ-∷ Γ→ eq pvΓ pvR = ?

TxoutC : Pred₀ Cfg
TxoutC Γ = ∀ {c v x} → ⟨ c , v ⟩at x ∈ᶜ Γ → TxInput′

ValuePreservingᶜ : Pred₀ (TxoutC Γ)
ValuePreservingᶜ {Γ} txoutC = ∀ {c v x} (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ) → txoutC c∈ ∙value ≡ v

ValuePreserving⇒ : ∀ (txout : Txout Γ) →
  ValuePreserving {Γ} txout
  ──────────────────────────────────────
  ValuePreservingᶜ {Γ} (txout ∘ c∈⇒x∈ Γ)
ValuePreserving⇒ {Γ} txout pv {c}{v}{x} c∈ =
  begin
    txout (c∈⇒x∈ Γ c∈) ∙value
  ≡⟨ pv _ ⟩
    (Γ , c∈⇒x∈ Γ c∈) ∙value
  ≡⟨ c∈⇒x∈∙value {Γ = Γ} c∈ ⟩
    v
  ∎

ValuePreservingʳᶜ : Pred₀ (ℝ R)
ValuePreservingʳᶜ {R} 𝕣 = ValuePreservingᶜ {R ∙cfg} (𝕣 ∙txoutC_)

{-
-- ValuePreservingʳ⇒ : ∀ (𝕣 :  R) (txout : Txout (𝕣 ∙cfg)) →
--   𝕣 ∙cfg ≡ Γ
--   ValuePreserving {𝕣 ∙cfg} txout
--   ──────────────────────────────
--   ValuePreservingʳ 𝕣
-}
