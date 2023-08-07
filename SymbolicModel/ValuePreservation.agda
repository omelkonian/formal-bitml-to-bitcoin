open import Prelude.Init
open L.Mem
open L.Perm using (∈-resp-↭)
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Lists.Collections
open import Prelude.Lists.Mappings
open import Prelude.Lists.Permutations
open import Prelude.Lists.MapMaybe

open import Bitcoin.Crypto
open import Bitcoin.Tx

open import BitML.BasicTypes using (⋯)

module SymbolicModel.ValuePreservation (⋯ : ⋯) where

open import Compiler.Mappings ⋯
open import SymbolicModel.Run ⋯ as S
  hiding (_∎; begin_)
open import SymbolicModel.Accessors ⋯
open import SymbolicModel.Collections ⋯
open import SymbolicModel.Mappings ⋯

open ≡-Reasoning

-- T0D0: identify a middle-point in the abstraction, where
-- we talk about value-preserving ???.
--   * 1. value preservation in each contract execution step
--   * 2. value preservation in Bitcoin ledgers
--   * 3. their correspondence
-- NB: this is *not* value-preservation as in the UTxO sense

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
