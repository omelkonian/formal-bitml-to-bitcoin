open import Prelude.Init; open SetAsType
open import Prelude.Lists.Mappings
open import Prelude.InferenceRules
open import Prelude.Traces
open import Prelude.Apartness
open import Prelude.Functor

open import SecureCompilation.ModuleParameters using (⋯)

module Coherence.Relation (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
open import ComputationalModel ⋯′ finPart keypairs as C
open import Coherence.Hypotheses ⋯

-- * Inductive case 1
data _⨾_⨾_~₁₁_⨾_ : StepRel where

  [1] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [2] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[2]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [3] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[3]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [4] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [5] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[5]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [6] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[6]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [7] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[7]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [8] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[8]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [9] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[9]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [10] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[10]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [11] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[11]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [12] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[12]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [13] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[13]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [14] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[14]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [15] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[15]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

  [18] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[18]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ

_⨾_⨾_≁₁₁_⨾_ : StepRel
Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁₁ λᶜ ⨾ Rᶜ = ¬ (Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ)

data _⨾_⨾_~₁₂_⨾_ : StepRel where

  [16] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[16]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₂ λᶜ ⨾ Rᶜ

  [17] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[17]~ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₂ λᶜ ⨾ Rᶜ

_⨾_⨾_≁₁₂_⨾_ : StepRel
Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁₂ λᶜ ⨾ Rᶜ = ¬ (Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₂ λᶜ ⨾ Rᶜ)

data _⨾_⨾_~₁_⨾_ : StepRel where

  [L]_ : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₁ λᶜ ⨾ Rᶜ
    ────────────────────────────────────
    Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁  λᶜ ⨾ Rᶜ

  [R] : ∀ {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    ∙ Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁₁ λᶜ ⨾ Rᶜ
    ∙ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁₂ λᶜ ⨾ Rᶜ
      ────────────────────────────────────
      Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁  λᶜ ⨾ Rᶜ

_⨾_⨾_≁₁_⨾_ : StepRel
Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁ λᶜ ⨾ Rᶜ = ¬ (Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ)

-- * Inductive case 2
data _~₂_∷ʳ_ : SRun → CRun → C.Label → Type where

  [1] : ∀ {Rˢ} {T : ∃Tx} (let 𝕣 = ℝ∗⇒ℝ (Rˢ .proj₂); open ℝ 𝕣) →
    T .proj₂ .proj₂ .inputs ♯ (hashTxⁱ <$> codom txout′)
    ────────────────────────────────────────────────────
    Rˢ ~₂ Rᶜ ∷ʳ submit T

  [2] : ∀ {Rˢ} →
    (λᶜ ≡ A →O∶ m) ⊎ (λᶜ ≡ O→ A ∶ m)
    ────────────────────────────────
    Rˢ ~₂ Rᶜ ∷ʳ λᶜ

  [2]′ : ∀ {Rˢ} →
    ────────────────────────────────
    Rˢ ~₂ Rᶜ ∷ʳ delay 0

  [3] : ∀ {𝕣∗ : ℝ∗ Rˢ} →
    let λᶜ = A →∗∶ m in
    -- λᶜ does not correspond to any symbolic move
    (∀ Γₜ λˢ → Γₜ ⨾ 𝕣∗ ⨾ λˢ ≁₁ λᶜ ⨾ Rᶜ)
    ───────────────────────────────────
    (-, 𝕣∗) ~₂ Rᶜ ∷ʳ λᶜ

data _~′_ : SRun → CRun → Type where

  -- * Base case
  base :
    ∀ {ℽ : ℾᵗ Γₜ₀} (let open ℾᵗ ℽ; Γ₀ = Γₜ₀ .cfg)
      -- (i) Rˢ = Γ₀ ∣ 0, with Γ₀ initial
      (init : Initial Γₜ₀)
      -- (ii) Rᶜ = T₀ ⋯ initial
      (cinit : Initial Rᶜ) →
      -- (iii) generation of public keys, we do not consider that here
      -- (iv) ⟨A,v⟩ₓ ∈ Γ₀ ⇒ txout{ x ↦ (v$ spendable with K̂(A)(rₐ)) ∈ T₀ }
    ∙ (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
        let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
        ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
               × (T₀ ‼ᵒ oᵢ ≡ v redeemable-by K̂ A))
      -- (v)  dom sechash = ∅
      -- (vi) dom κ       = ∅
      -- by definition of Initial/ℝ
      ──────────────────────────────────────────────────────────────────────
      (-, ℽ ∎⊣ init ✓) ~′ Rᶜ

  -- * Inductive case 1
  step₁ : ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    ∙ (-, 𝕣∗) ~′ Rᶜ
    ∙ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ
      ──────────────────────────────────
      (-, Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~′ (λᶜ ∷ Rᶜ ✓)

  -- * Inductive case 2
  step₂ : ∀ {Rˢ} →
    ∙ Rˢ ~′ Rᶜ
    ∙ Rˢ ~₂ Rᶜ ∷ʳ λᶜ
      ─────────────────
      Rˢ ~′ (λᶜ ∷ Rᶜ ✓)

_~_ _≁_ : S.Run → CRun → Type
Rˢ ~ Rᶜ = ∃ λ (𝕣∗ : ℝ∗ Rˢ) → (-, 𝕣∗) ~′ Rᶜ
_≁_ = ¬_ ∘₂ _~_

pattern [L1]_ h = [L] [1] h
pattern [L2]_ h = [L] [2] h
pattern [L3]_ h = [L] [3] h
pattern [L4]_ h = [L] [4] h
pattern [L5]_ h = [L] [5] h
pattern [L6]_ h = [L] [6] h
pattern [L7]_ h = [L] [7] h
pattern [L8]_ h = [L] [8] h
pattern [L9]_ h = [L] [9] h
pattern [L10]_ h = [L] [10] h
pattern [L11]_ h = [L] [11] h
pattern [L12]_ h = [L] [12] h
pattern [L13]_ h = [L] [13] h
pattern [L14]_ h = [L] [14] h
pattern [L15]_ h = [L] [15] h
pattern [L18]_ h = [L] [18] h
pattern [R16⊣_]_ ¬coh h = [R] ¬coh ([16] h)
pattern [R17⊣_]_ ¬coh h = [R] ¬coh ([17] h)

-- ** DSL for presenting coherence steps
infix 0 ∎_⊣_,_~_⊣_⊣_
∎_⊣_,_~_⊣_⊣_ :
  ∀ Γₜ₀ (init : Initial Γₜ₀) (ℽ₀ : ℾᵗ Γₜ₀) →
  ∀ (rᶜ : C.Run) (cinit : Initial rᶜ) →
  let open ℾᵗ ℽ₀; Γ₀ = Γₜ₀ .cfg in
  (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
      let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
      ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
            × (T₀ ‼ᵒ oᵢ ≡ v redeemable-by K̂ A))
  → (Γₜ₀ ∎⊣ init) ~ (rᶜ ∎⊣ cinit ✓)
∎ Γₜ ⊣ init , ℽ₀ ~ Rᶜ ⊣ cinit ⊣ txout≈ =
  -, base {ℽ = ℽ₀} init cinit txout≈

infixl -1 _—→_⊣_~_⊣_ _—→ᵋ_⊣_
_—→_⊣_~_⊣_ : ∀ {Rˢ Rᶜ} (coh : Rˢ ~ Rᶜ) Γₜ (λˢ : 𝕃 Rˢ Γₜ) λᶜ →
  Γₜ ⨾ coh .proj₁ ⨾ λˢ ~₁ λᶜ ⨾ Rᶜ
  ──────────────────────────────────────────
  (Γₜ ∷ Rˢ ⊣ λˢ .proj₁)       ~  (λᶜ ∷ Rᶜ ✓)
(𝕣∗ , coh) —→ Γₜ ⊣ λˢ ~ λᶜ ⊣ p =
  Γₜ ∷ 𝕣∗ ⊣ λˢ ✓ , step₁ {λˢ = λˢ} coh p

_—→ᵋ_⊣_ : ∀ {Rˢ Rᶜ} (coh : Rˢ ~ Rᶜ) λᶜ →
  (-, coh .proj₁) ~₂ Rᶜ ∷ʳ λᶜ
  ──────────────────────────────
  Rˢ              ~  (λᶜ ∷ Rᶜ ✓)
(𝕣∗ , coh) —→ᵋ λᶜ ⊣ p
  = 𝕣∗ , step₂ coh p

private
  testPatternMatch-~ : Rˢ ~ Rᶜ → ⊤
  testPatternMatch-~ (𝕣∗ , coh) with coh
  ... | base init cinit txout≈ = tt
  ... | step₂ _ ([1] ins♯) = tt
  ... | step₂ _ ([2] λᶜ≡) = tt
  ... | step₂ _ [2]′ = tt
  ... | step₂ _ ([3] ¬p) = tt
  ... | step₁ _ p with p
  ... | [L1]  h = tt
  ... | [L2]  h = tt
  ... | [L3]  h = tt
  ... | [L4]  h = tt
  ... | [L5]  h = tt
  ... | [L6]  h = tt
  ... | [L7]  h = tt
  ... | [L8]  h = tt
  ... | [L9]  h = tt
  ... | [L10] h = tt
  ... | [L11] h = tt
  ... | [L12] h = tt
  ... | [L13] h = tt
  ... | [L14] h = tt
  ... | [L15] h = tt
  ... | [R16⊣ ¬coh ] h = tt
  ... | [R17⊣ ¬coh ] h = tt
  ... | [L18] h = tt
