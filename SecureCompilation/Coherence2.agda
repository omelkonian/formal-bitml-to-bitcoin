open import Prelude.Init hiding (T)
open L.Mem
open import Prelude.Lists
open import Prelude.General
open import Prelude.DecLists
open import Prelude.DecEq

open import Prelude.Collections
open import Prelude.Monoid

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Ord
open import Prelude.ToN
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.InferenceRules

open import Bitcoin.Crypto using (KeyPair)

module SecureCompilation.Coherence2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (_∎; begin_; d; Γₜ″)

open import ComputationalModel Participant Honest finPart keypairs as C
  hiding (Hon; Initial; Σ
         ; t; t′; `; ∣_∣; n)

open import SecureCompilation.Compiler Participant Honest η

private
  variable
    ⟨G⟩C ⟨G⟩C′ ⟨G⟩C″ : Ad
    T T′ : ∃Tx

    𝕣  : ℝ Rˢ
    ∃𝕣 ∃𝕣′ : ∃ ℝ

postulate
  encode : Txout Rˢ → Ad → Message
  -- ^ encode {G}C as a bitstring, representing each x in it as txout(x)

  SIGᵖ : ∀ {A : Set} → ℤ {- public key -} → A → ℤ

  ∣_∣ᶻ : ℤ → ℕ
  ∣_∣ᵐ : Message → ℕ

_-redeemableWith-_ : S.Value → KeyPair → ∃TxOutput
v -redeemableWith- k = Ctx 1 , record {value = v;  validator = ƛ (versig [ k ] [ # 0 ])}

-- T0D0: redefine Message ≈ ℤ ??
SIGᵐ : KeyPair → Message → Message
SIGᵐ k = map (SIG k)

-- Convenient wrapper for calling the BitML compiler.
COMPILE : 𝔾 ad → ∃Tx¹ × (subtermsᵃ′ ad ↦′ ∃Txᶜ ∘ removeTopDecorations)
COMPILE {ad = ad} (vad , txout₀ , sechash₀ , κ₀) =
  let
    K : 𝕂 (ad .G)
    K {p} _ = K̂ p

    T , ∀d = bitml-compiler {ad = ad} vad sechash₀ txout₀ K κ₀
  in
    T , (∀d ∘ h-subᶜ {ds = ad .C})

-- * Inductive case 1

data _~₁₁_ : ℝ∗ Rˢ → C.Run → Set where

  -- ** Stipulation: advertisting a contract
  [1] : ∀ {𝕣∗ : ℝ∗ Rˢ} →
      let
        𝕣 = ℝ∗⇒ℝ 𝕣∗
        open ℝ 𝕣
        ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = advertise⦅ ⟨G⟩C ⦆
        Γ′  = ` ⟨G⟩C ∣ Γ
        t′  = t
        Γₜ′ = Γ′ at t′

        C  = encode {Rˢ} txout′ ⟨G⟩C
        λᶜ = A →∗∶ C
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) → let Γₜ″ = ∃Γ≈ .proj₁ at t′ in
      -- Hypotheses from [C-Advertise]
      (vad : Valid ⟨G⟩C)
      (hon : Any (_∈ Hon) partG)
      (d⊆  : ⟨G⟩C ⊆⦅ deposits ⦆ Γ)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

        -- txout′ = txout, sechash′ = sechash, κ′ = κ
        open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈ using (𝕒ℽ)
      in
      --——————————————————————————————————————————————————————————————————————
      (Γₜ″ ∷ 𝕣∗ ⊣ 𝕒ℽ ✓) ~₁₁ (λᶜ ∷ Rᶜ)

data _~₁_ : ℝ∗ Rˢ → C.Run → Set where

  [L]_ : ∀ {𝕣∗ : ℝ∗ Rˢ} {𝕒ℽ : 𝔸ℾ Rˢ Γₜ} →
    (Γₜ ∷ 𝕣∗ ⊣ 𝕒ℽ ✓) ~₁₁ (λᶜ ∷ Rᶜ)
    ──────────────────────────────
    (Γₜ ∷ 𝕣∗ ⊣ 𝕒ℽ ✓) ~₁  (λᶜ ∷ Rᶜ)

data _~~_ : ℝ∗ Rˢ → C.Run → Set where

  -- * Base case
  base : ∀ {ℽ : ℾᵗ Γₜ₀} → let open ℾᵗ ℽ; Γ₀ = Γₜ₀ .cfg in

      -- (i) Rˢ = Γ₀ ∣ 0, with Γ₀ initial
    ∀ (init : Initial Γₜ₀) →
      -- (ii) Rᶜ = T₀ ⋯ initial
    ∀ (cinit : C.Initial Rᶜ) →
      -- (iv) ⟨A,v⟩ₓ ∈ Γ₀ ⇒ txout{ x ↦ (v$ spendable with K̂(A)(rₐ)) ∈ T₀ }
    ∙ (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
        let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
        ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
               × (T₀ ‼ᵒ oᵢ ≡ v -redeemableWith- K̂ A))
      -- (v)  dom sechash = ∅
      -- (vi) dom κ       = ∅
      -- by definition of Initial/ℝ
      ──────────────────────────────────────────────────────────────────────
      (ℽ ∎⊣ init ✓) ~~ Rᶜ


  -- * Inductive case 1
  step₁ : ∀ {𝕣∗ : ℝ∗ Rˢ} {𝕒ℽ : 𝔸ℾ Rˢ Γₜ} →
    ∙ 𝕣∗ ~~ Rᶜ
    ∙ (Γₜ ∷ 𝕣∗ ⊣ 𝕒ℽ ✓) ~₁ (λᶜ ∷ Rᶜ)
      ────────────────────────
      (Γₜ ∷ 𝕣∗ ⊣ 𝕒ℽ ✓) ~~ (λᶜ ∷ Rᶜ)

_~_ _≁_ : S.Run → C.Run → Set
Rˢ ~ Rᶜ = ∃ λ (𝕣∗ : ℝ∗ Rˢ) → 𝕣∗ ~~ Rᶜ
_≁_ = ¬_ ∘₂ _~_

private
  -- testPatternMatch-~₁ : ∀ {λˢ : 𝕃 Rˢ Γₜ}
  --   → (Rˢ ⦊ λˢ) ~₁ (Rᶜ ⦊ λᶜ)
  --   → ⊤
  -- testPatternMatch-~₁ coh
  --   with coh
  -- ... | [L] [1]  R≈ ∃Γ≈ vad hon d⊆ = tt

  -- testPatternMatch-~′ : ∀ (𝕣 : ℝ Rˢ)
  --   → (-, 𝕣) ~′ Rᶜ
  --   → ⊤
  -- testPatternMatch-~′ 𝕣 coh
  --   with coh
  -- ... | step₁ _ p
  --   with p
  -- ... | [L] [1]  R≈ ∃Γ≈ vad hon d⊆ = tt


  testPatternMatch-~ : Rˢ ~ Rᶜ → ⊤
  testPatternMatch-~ (𝕣∗ , coh)
    with coh
  ... | base init cinit txout≈ = tt
  ... | step₁ _ ([L] [1] R≈ ∃Γ≈ vad hon d⊆) = tt
