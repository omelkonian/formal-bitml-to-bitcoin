{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding (T); open SetAsType
open L.Mem
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Membership.Patterns
open import Prelude.Lists
open import Prelude.Lists.Collections
open import Prelude.Lists.Dec
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Traces
open import Prelude.Null
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Num

open import SecureCompilation.ModuleParameters using () renaming (⋯ to $⋯)
module Coherence.ValuePreservation ($⋯ : $⋯) (open $⋯ $⋯) where

open import SymbolicModel ⋯′ as S
  hiding ( _∎; begin_
         {-variables-}
         ; Γ₀; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; Δ
         ; R; R′; Rˢ; Rˢ′
         ; A; B; B′
         ; G; C
         ; t; t′; δ; n
         ; ad; g; c; c′; cs; ds; d; vcs
         ; x; x′; y; y′; z; xs
         ; a; as
         ; v; v′; vs
         ; α; p; Σ
         )
open import ComputationalModel ⋯′ finPart keypairs
  hiding ( `; ∣_∣; _`∧_; _`∨_; _`=_; _`<_; `true; ∎
         ; Run; Time; Value; DecEq-Label
         ; HonestMoves; HonestStrategies; ParticipantStrategy
         ; Valid-Strategy; moves
         ; Σ
         ; module AdvM
         {-variables-}
         ; R; R′; R″; Rᶜ
         ; tx; i; t; t′; n; m; m′; λᶜ
         )
  renaming (Label to CLabel; Labels to CLabels)
open import Compiler ⋯′ η
open import Coherence.ComputationalContracts ⋯′
open import Coherence.Helpers $⋯
open import Coherence.Hypotheses $⋯

open ≡-Reasoning

module V₁ (⋯ : H₁-args) (open H₁-args ⋯) (open H₁ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = pv-txout′
    where
    open ≡-Reasoning

    txoutΓ : Txout (R .end)
    txoutΓ = 𝕣 ∙txoutEnd_

    txoutΓ′ : Txout Γ′
    txoutΓ′ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ

    pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
    pv-txoutΓ′ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ pv-txout

    txoutΓ″ : Txout Γ″
    txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

    pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
    pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

    pv-txout′ : ValuePreservingʳ 𝕣′
    pv-txout′ x∈ =
      begin
        (𝕣′ ∙txoutEnd x∈) ∙value
      ≡⟨ cong _∙value $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
        (txoutΓ″ x∈) ∙value
      ≡⟨ pv-txoutΓ″ _ ⟩
        (Γ″ , x∈) ∙value
      ∎

module V₂ (⋯ : H₂-args) (open H₂-args ⋯) (open H₂ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = pv-txout′
    where
    open ≡-Reasoning

    txoutR : Txout (R ∙cfg)
    txoutR = 𝕣 ∙txoutEnd_

    txoutΓ : Txout Γ
    txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutR

    pv-txoutΓ : ValuePreserving {Γ} txoutΓ
    pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutR pv-txout

    txoutΓ′ : Txout Γ′
    txoutΓ′ = txout↝ txoutΓ

    pv↝ : ValuePreserving↝ {Γ}{Γ′} txout↝
    pv↝ txoutΓ pv-txoutΓ {x} x∈
      with ∈-ids-++⁻ (Γ ∣ mkRev Δ) (A auth[ ♯▷ ad ]) x∈
    ... | inj₂ ()
    ... | inj₁ x∈
      with ∈-ids-++⁻ Γ (mkRev Δ) x∈
    ... | inj₂ x∈ = contradict $ x∈ :~ hʳ Δ ⟪ x L.Mem.∈_ ⟫
      where
      hʳ : ∀ Δ → Null $ ids (mkRev Δ)
      hʳ [] = refl
      hʳ (_ ∷ []) = refl
      hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _
    ... | inj₁ x∈ = pv-txoutΓ x∈

    pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
    pv-txoutΓ′ = pv↝ txoutΓ pv-txoutΓ

    txoutΓ″ : Txout Γ″
    txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

    pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
    pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

    pv-txout′ : ValuePreservingʳ 𝕣′
    pv-txout′ x∈ =
      begin
        (𝕣′ ∙txoutEnd x∈) ∙value
      ≡⟨ cong _∙value $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
        (txoutΓ″ x∈) ∙value
      ≡⟨ pv-txoutΓ″ _ ⟩
        (Γ″ , x∈) ∙value
      ∎

module V₃ (⋯ : H₃-args) (open H₃-args ⋯) (open H₃ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₄ (⋯ : H₄-args) (open H₄-args ⋯) (open H₄ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₅ (⋯ : H₅-args) (open H₅-args ⋯) (open H₅ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₆ (⋯ : H₆-args) (open H₆-args ⋯) (open H₆ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = pv-txout′
    where
    txoutΓ : Txout Γ
    txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

    pv-txoutΓ : ValuePreserving {Γ} txoutΓ
    pv-txoutΓ =
      ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

    txoutΓ₂ : Txout Γ₂
    txoutΓ₂ = weaken-↦ txoutΓ p⊆

    pv-txoutΓ₂ : ValuePreserving {Γ₂} txoutΓ₂
    pv-txoutΓ₂ x∈ =
      begin
        txoutΓ₂ x∈ ∙value
      ≡⟨⟩
        weaken-↦ txoutΓ p⊆ x∈ ∙value
      ≡⟨ pv-weaken-↦ {Γ}{Γ₂} txoutΓ p⊆ pv⊆ pv-txoutΓ x∈ ⟩
        (Γ₂ , x∈) ∙value
      ∎ where open ≡-Reasoning
              pv⊆ : ValuePreserving⊆ {Γ₂}{Γ} p⊆
              pv⊆ x∈ =
                begin
                  (Γ₂ , x∈) ∙value
                ≡˘⟨ ∈-ids-++⁺ʳ∙value {Γ′ = Γ₂}{Γ₁} x∈ ⟩
                  (Γ₁ ∣ Γ₂ , ∈-ids-++⁺ʳ Γ₁ Γ₂ x∈) ∙value
                ≡⟨⟩
                  (Γ , there (∈-ids-++⁺ʳ Γ₁ Γ₂ x∈)) ∙value
                ≡⟨⟩
                  (Γ , p⊆ x∈) ∙value
                ∎

    txoutΓ′ : Txout Γ′
    txoutΓ′ = txout↝ txoutΓ

    pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
    pv-txoutΓ′ = pv-cons-↦ val≡ pv-txoutΓ₂

    txoutΓ″ : Txout Γ″
    txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

    pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
    pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

    pv-txout′ : ValuePreservingʳ 𝕣′
    pv-txout′ x∈ =
      begin
        (𝕣′ ∙txoutEnd x∈) ∙value
      ≡⟨ cong _∙value
            $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
        (txoutΓ″ x∈) ∙value
      ≡⟨ pv-txoutΓ″ _ ⟩
        (Γ″ , x∈) ∙value
      ∎

module V₇ (⋯ : H₇-args) (open H₇-args ⋯) (open H₇ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!S.ss!}

module V₈ (⋯ : H₈-args) (open H₈-args ⋯) (open H₈ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₉ (⋯ : H₉-args) (open H₉-args ⋯) (open H₉ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₀ (⋯ : H₁₀-args) (open H₁₀-args ⋯) (open H₁₀ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₁ ($⋯ : H₁₁-args) (open H₁₁-args $⋯) (tx : TxInput′) (open H₁₁ $⋯ tx) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  module _ {c v x} where
    private
      c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
          → R  ≈⋯ ⟨ c , v ⟩at x ⋯
      c∈⇐ = {!!}
    abstract
      txoutEndC≡ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″) →
        𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC (c∈⇐ c∈)
      txoutEndC≡ c∈ =
        begin
          𝕣′ ∙txoutC c∈
        ≡⟨⟩
          𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
        -- ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
        --   𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
        -- ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
        --   𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
        ≡⟨ {!!} ⟩
          𝕣 ∙txoutC (c∈⇐ c∈)
        ∎ where open ≡-Reasoning

module V₁₂ (⋯ : H₁₂-args) (open H₁₂-args ⋯) (open H₁₂ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₃ (⋯ : H₁₃-args) (open H₁₃-args ⋯)
           (tx tx′ : TxInput′) (open H₁₃ ⋯ tx tx′) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₄ (⋯ : H₁₄-args) (open H₁₄-args ⋯) (open H₁₄ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₅ (⋯ : H₁₅-args) (open H₁₅-args ⋯) (tx : TxInput′) (open H₁₅ ⋯ tx) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₆ (⋯ : H₁₆-args) (open H₁₆-args ⋯) (open H₁₆ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = {!!}

module V₁₇ (⋯ : H₁₇-args) (open H₁₇-args ⋯) (open H₁₇ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)
  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = pv-txout′
    where
      open ≡-Reasoning

      txoutΓ : Txout Γ
      txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

      pv-txoutΓ : ValuePreserving {Γ} txoutΓ
      pv-txoutΓ =
        ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

      postulate pv↝ : ValuePreserving↝ {Γ}{Γ′} txout↝
      -- pv↝ txoutΓ pv-txoutΓ {x} x∈
      --   = ?

      txoutΓ′ : Txout Γ′
      txoutΓ′ = txout↝ txoutΓ

      pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
      pv-txoutΓ′ =  pv↝ txoutΓ pv-txoutΓ

      txoutΓ″ : Txout Γ″
      txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

      pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
      pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

      pv-txout′ : ValuePreservingʳ 𝕣′
      pv-txout′ x∈ =
        begin
          (𝕣′ ∙txoutEnd x∈) ∙value
        ≡⟨ cong _∙value
              $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
          (txoutΓ″ x∈) ∙value
        ≡⟨ pv-txoutΓ″ _ ⟩
          (Γ″ , x∈) ∙value
        ∎

module V₁₈ (⋯ : H₁₈-args) (open H₁₈-args ⋯) (open H₁₈ ⋯) where
  𝕣′ : ℝ R′
  𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  value-preserving⇒ :
    ValuePreservingʳ 𝕣
    ───────────────────
    ValuePreservingʳ 𝕣′
  value-preserving⇒ pv-txout = pv-txout′
    where
      open ≡-Reasoning

      txoutΓ : Txout Γ
      txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

      pv-txoutΓ : ValuePreserving {Γ} txoutΓ
      pv-txoutΓ =
        ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

      txoutΓ′ : Txout Γ′
      txoutΓ′ = txoutΓ

      pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
      pv-txoutΓ′ = pv-txoutΓ

      txoutΓ″ : Txout Γ″
      txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

      pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
      pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

      pv-txout′ : ValuePreservingʳ 𝕣′
      pv-txout′ x∈ =
        begin
          (𝕣′ ∙txoutEnd x∈) ∙value
        ≡⟨ cong _∙value
              $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
          (txoutΓ″ x∈) ∙value
        ≡⟨ pv-txoutΓ″ _ ⟩
          (Γ″ , x∈) ∙value
        ∎
