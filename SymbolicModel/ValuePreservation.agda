-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open L.Mem
open L.Perm using (∈-resp-↭)
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Collections
open import Prelude.Lists.Mappings

open import Bitcoin.Crypto
open import Bitcoin.Tx

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

open import ComputationalModel.Accessors using (_∙value)

TxoutC : Pred₀ Cfg
TxoutC Γ = ∀ {c v x} → ⟨ c , v ⟩at x ∈ᶜ Γ → TxInput′

ValuePreserving′ : ∀ (xs : Ids) → Pred₀ (xs ↦ TxInput′)
ValuePreserving′ xs txout = ∀ {x} (x∈ : x ∈ xs) → txout x∈ ∙value ≡ {!!}

ValuePreserving : Pred₀ (TxoutC Γ)
ValuePreserving {Γ} txoutC =
  ∀ {c v x} (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ) → txoutC c∈ ∙value ≡ v

ValuePreservingₓ : Pred₀ (Txout Γ)
ValuePreservingₓ {Γ} txout = ValuePreserving {Γ} (txout ∘ c∈⇒x∈ Γ)

ValuePreserving⇒ : ∀ (Γ≈ : Γ ≈ Γ′) (txoutC : TxoutC Γ′) →
  ValuePreserving {Γ′} txoutC
  ───────────────────────────────────────────────────
  ValuePreserving {Γ} (txoutC ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈)
ValuePreserving⇒ {Γ}{Γ′} Γ≈ _ pv = pv ∘ ∈ᶜ-resp-≈ {Γ}{Γ′} Γ≈

ValuePreserving≗ : ∀ (txoutC txoutC′ : TxoutC Γ) →
  -- ∙ txoutC ≗ txoutC′
  ∙ (∀ {c v x} (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ) → txoutC c∈ ≡ txoutC′ c∈)
  ∙ ValuePreserving {Γ} txoutC
    ───────────────────────────
    ValuePreserving {Γ} txoutC′
ValuePreserving≗ _ _ eq pv {v = v} c∈ = pv c∈ :~ eq c∈ ⟪ (λ ◆ → ◆ ∙value ≡ v) ⟫

ValuePreservingₓ-Txout≈ : (Γ≈ : Γ ≈ Γ′) (txout : Txout Γ) →
  ValuePreservingₓ {Γ} txout
  ───────────────────────────────────────────────
  ValuePreservingₓ {Γ′} (Txout≈ {Γ}{Γ′} Γ≈ txout)
ValuePreservingₓ-Txout≈ {Γ}{Γ′} Γ≈ txout pv {v = v} c∈ =
  begin
    Txout≈ {Γ}{Γ′} Γ≈ txout (c∈⇒x∈ Γ′ c∈) ∙value
  ≡⟨⟩
    txout (∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) $ c∈⇒x∈ Γ′ c∈) ∙value
  ≡⟨ cong (λ ◆ → txout ◆ ∙value)
     $ begin
         ∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) (c∈⇒x∈ Γ′ c∈)
       ≡⟨ cong (λ ◆ → ∈-resp-↭ ◆ (c∈⇒x∈ Γ′ c∈)) $ ↭-sym∘≈⇒namesʳ↭ {Γ}{Γ′} Γ≈ ⟩
         ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ} $ ↭-sym Γ≈) (c∈⇒x∈ Γ′ c∈)
       ≡⟨ ∈-resp-↭∘c∈⇒x∈ Γ′ Γ (↭-sym Γ≈) c∈ ⟩
         c∈⇒x∈ Γ (∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈) c∈)
       ∎ ⟩
    txout (c∈⇒x∈ Γ (∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈) c∈)) ∙value
  ≡⟨ pv (∈ᶜ-resp-≈ {Γ′}{Γ} (↭-sym Γ≈) c∈) ⟩
    v
  ∎ where open ≡-Reasoning

pv-cons-↦ : ∀ (txoutΓ : Txout Γ) (y : Id) (tx : TxInput′) →
  ValuePreservingₓ {Γ} txoutΓ
  ──────────────────────────────────────
  ValuePreservingₓ {⟨ c , tx ∙value ⟩at y ∣ Γ} (cons-↦ y tx txoutΓ)
pv-cons-↦ {Γ}{c} txoutΓ y tx pv c∈
  with c∈ | c∈⇒x∈ (⟨ c , tx ∙value ⟩at y ∣ Γ) c∈
... | here refl | p = {!p!}
... | there c∈  | p = {!!}
--   with c∈ | c∈⇒x∈ (⟨ c , tx ∙value ⟩at y ∣ Γ) c∈
-- ... | here refl | .here _ = {!eq!}
-- ... | there _   | .there x∈ = {!pv !} -- pv (c∈⇒x∈ x∈

open import Prelude.Decidable
{- DOES NOT HOLD
c∈-ids≡ :
  ∙ Γ ≡⦅ ids ⦆ Γ′
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
    ────────────────────
    ⟨ c , v ⟩at x ∈ᶜ Γ′
c∈-ids≡ {` ad} ids≡ c∈ = contradict c∈
c∈-ids≡ {⟨ c , v ⟩at x} ids≡ c∈ = {!!}
c∈-ids≡ {⟨ A has v ⟩at x} ids≡ c∈ = contradict c∈
c∈-ids≡ {A auth[ a ]} ids≡ c∈ = contradict c∈
c∈-ids≡ {⟨ A ∶ s ♯ mn ⟩} ids≡ c∈ = contradict c∈
c∈-ids≡ {A ∶ s ♯ n} ids≡ c∈ = contradict c∈
c∈-ids≡ {Γ ∣ Γ₁} ids≡ c∈ = {!!}
-}

-- subst∘c∈⇒x∈ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ′) (ids≡ : Γ ≡⦅ ids ⦆ Γ′) (txout : Txout Γ)
--   → (txout :~ ids≡ ⟪ _↦ TxInput′ ⟫) (c∈⇒x∈ Γ′ c∈)
--   ≡ txout (c∈⇒x∈ Γ (c∈-ids≡ {Γ′}{Γ} (sym ids≡) c∈))
-- subst∘c∈⇒x∈ {c}{v}{x}{Γ′}{Γ} c∈ ids≡ txout = {!!}

pv-subst-↦ : ∀ (txout : Txout Γ) (ids≡ : Γ ≡⦅ ids ⦆ Γ′) →
  ValuePreservingₓ {Γ} txout
  ────────────────────────────────────────────────────
  ValuePreservingₓ {Γ′} (txout :~ ids≡ ⟪ _↦ TxInput′ ⟫)
pv-subst-↦ {Γ}{Γ′} txout ids≡ pv {c}{v}{x} c∈ =
  begin
    (txout :~ ids≡ ⟪ _↦ TxInput′ ⟫) (c∈⇒x∈ Γ′ c∈) ∙value
  -- ≡⟨ cong _∙value $ subst∘c∈⇒x∈ {c}{v}{x}{Γ′}{Γ} c∈ ids≡ txout ⟩
  ≡⟨ {!!} ⟩
    -- txout (c∈⇒x∈ Γ (c∈-ids≡ {Γ′}{Γ} (sym ids≡) c∈)) ∙value
    txout (⟪ x L.Mem.∈_ ⟫ ids≡ ~: c∈⇒x∈ Γ′ c∈) ∙value
  ≡⟨ {!!} ⟩
    txout {!⟪ (λ ◆ → _ ∈ ◆) ⟫ ids≡ ~: c∈⇒x∈ Γ′ c∈ !} ∙value
  ≡⟨ pv _ ⟩
    v
  ∎ where open ≡-Reasoning


--   -- ValuePreservingᵢₛ : ∀ {is : Ids} → Pred₀ (ids ↦ TxInput′)
--   -- ValuePreservingᵢₛ {is} f = ∀ x∈ → f x∈ ≡ ValuePreserving {Γ} (txout ∘ c∈⇒x∈ Γ)

--   postulate pv-txoutC : ValuePreserving {R ∙cfg} (𝕣 ∙txoutC_)

--   pv-txoutΓ : ValuePreservingₓ {Γ} txoutΓ
--   pv-txoutΓ = ValuePreservingₓ-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txoutC

--   -- pv-subst-↦ : ∀ {Γ} {is} (txoutΓ : Txout Γ) (ids≡ : ids Γ ≡ is) →
--   --   ValuePreservingₓ {Γ} txoutΓ
--   --   ────────────────────────────────────────────────────
--   --   (∀ ? → (txoutΓ :~ ids≡ ⟪ _↦ TxInput′ ⟫) ∘ ∘ c∈⇒x∈ )  ∙value ≡ v)
--   -- pv-subst-↦ {Γ} txoutΓ ids≡ pv = {!!}

--   -- pv-weaken-↦ : ∀ (txout : ids Γ₁ ++ ids Γ₀ ↦ TxInput′)
--   --   ValuePreservingₓ {Γ₀} txout
--   --   ─────────────────────────────────────
--   --   ValuePreservingₓ {Γ₀} (weaken-↦ txout (∈-++⁺ʳ _))
--   -- pv-weaken-↦ = {!!}

--   pv-txoutΓ₀ : ValuePreservingₓ {Γ₀} txoutΓ₀
--   pv-txoutΓ₀ = {!pv-txoutΓ ?!}
