-----------------------------------------------
-- Parsing computational runs to symbolic ones.
-----------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding (T)
open L.Mem using (_∈_; ∈-map⁻)
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership hiding (_∈_)
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.InferenceRules
open import Prelude.Lists.Collections
open import Prelude.Semigroup
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.General
open import Prelude.Tactics.Existentials

open import Bitcoin using (KeyPair)

module SecureCompilation.Backtranslation.Parsing
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (Rˢ′; d)
open import ComputationalModel Participant Honest finPart keypairs as C
  hiding (Hon; Initial; Σ
         ; t; t′; `; ∣_∣; n)

open import SecureCompilation.Helpers  Participant Honest finPart keypairs η
open import SecureCompilation.Coherence Participant Honest finPart keypairs η as SC

open import SecureCompilation.Backtranslation.Parsing.Views Participant Honest finPart keypairs η

parseRun : (Rᶜ : CRun) → ∃ (_~ Rᶜ)
parseRun (Rᶜ ∎⊣ init ✓) = ∅ˢ , ℝ∗-∅ˢ , base auto init (λ ())
parseRun ((A →O∶  m) ∷ Rᶜ ✓) =
  let Rˢ , 𝕣 , Rˢ~Rᶜ = parseRun Rᶜ
  in  Rˢ , 𝕣 , step₂ Rˢ~Rᶜ ([2] $′ inj₁ refl)
parseRun ((O→ A ∶ m) ∷ Rᶜ ✓) =
  let Rˢ , 𝕣 , Rˢ~Rᶜ = parseRun Rᶜ
  in  Rˢ , 𝕣 , step₂ Rˢ~Rᶜ ([2] $′ inj₂ refl)
parseRun (delay δ ∷ Rᶜ ✓)
  with δ >? 0
... | yes δ>0
  -- [18]
  = let
      Rˢ , 𝕣∗ , Rˢ~Rᶜ = parseRun Rᶜ
      𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

      Γₜ@(Γ at t) = Rˢ .end
      α   = delay⦅ δ ⦆
      t′  = t + δ
      Γₜ′ = Γ at t′
      -- λᶜ  = delay δ

      ∃Γ≈ : ∃ (_≈ᶜ Γ)
      ∃Γ≈ = Γ , ↭-refl

      Γₜ″ = ∃Γ≈ .proj₁ at t′

      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Delay] δ>0

      open H₁₈ {Rˢ} 𝕣 t α t′ Γ (≈ᵗ-refl {Γₜ}) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
      -, (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) , step₁ Rˢ~Rᶜ ([L] [18] δ>0 ∃Γ≈)
... | no  δ≯0
  -- [T0D0] cannot use [R] [3] as it only covers `A →∗∶ m` messages, not delays
  = {!!}

parseRun ((A₀ →∗∶ m₀) ∷ Rᶜ ✓)
  with Rˢ , 𝕣∗ , Rˢ~Rᶜ ← parseRun Rᶜ
  with decodeBroadcast Rˢ 𝕣∗ Rᶜ A₀ m₀
... | [1] ⟨G⟩C (vad , hon , d⊆ , refl) =
  let
    Γₜ@(Γ at t) = Rˢ .end

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    Γ′  = ` ⟨G⟩C ∣ Γ

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [1] {Γ = Γ} R≈ ∃Γ≈ vad hon d⊆)
... | [2] ⟨G⟩C Δ×h̅ k⃗ A Γ₀ t (R≈ , as≡ , All∉ , Hon⇒ , ∃B , h≡ , h∈O , unique-h , h♯sechash , refl) =
  let
    Γ = ` ⟨G⟩C ∣ Γ₀
    Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅
    Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ
    Γ′  = Γ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [2] {Γ₀ = Γ₀} R≈ ∃Γ≈ as≡ All∉ Hon⇒ ∃B h≡ h∈O unique-h h♯sechash)
... | [3] ⟨G⟩C Γ₀ t A v x (R≈ , committedA , A∈per , ∃B , refl) =
  let
    Γ  = ` ⟨G⟩C ∣ Γ₀
    Γ′ = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [3] R≈ ∃Γ≈ committedA A∈per ∃B)
{-
... | [5] A v x Γ₀ t c i (D≡A:D′ , R≈ , refl) =
  let
    open ∣SELECT c i
    Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [5] D≡A:D′ R≈ ∃Γ≈)
... | [7] ⟨G⟩C A a n Γ₀ t Δ×h̅ k⃗ (m≤ , R≈ , ∃B , ∃α , a∈ , ∃λ , first-λᶜ) =
  let
    Γ′  = A ∶ a ♯ n ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [7] {Γ₀ = Γ₀} m≤ R≈ ∃Γ≈ ∃B ∃α a∈ ∃λ first-λᶜ)
... | [10] A v x v′ x′ Γ₀ t (R≈ , ∃λ , first-λᶜ , refl) =
  let
    Γ′ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [10] {Γ₀ = Γ₀} R≈ ∃Γ≈ ∃λ first-λᶜ)
... | [12] A v v′ x Γ₀ t (R≈ , ∃λ , first-λᶜ , refl) =
  let
    Γ′ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [12] {Γ₀ = Γ₀} R≈ ∃Γ≈ ∃λ first-λᶜ)
... | [14] A v x Γ₀ t B′ (R≈ , ∃λ , first-λᶜ , refl) =
  let
    Γ′ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [14] {Γ₀ = Γ₀} R≈ ∃Γ≈ ∃λ first-λᶜ)
... | [16] ds j y Γ₀ t B′ i (R≈ , fresh-y , T , ⊆ins , T∈ , first-λᶜ , ¬coh , refl , refl) =
  let
    xs = map (proj₂ ∘ proj₂) ds
    A  = proj₁ (ds ‼ j)
    j′ = ‼-map {xs = ds} j
    Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
    Γ′ = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([R] [16] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y T ⊆ins T∈ first-λᶜ ¬coh)
-}
... | FAIL ¬coh = -, 𝕣∗ , step₂ Rˢ~Rᶜ ([3] ¬coh)

parseRun (submit T₀ ∷ Rᶜ ✓)
  with Rˢ , 𝕣∗ , Rˢ~Rᶜ ← parseRun Rᶜ
  with decodeTx Rˢ 𝕣∗ Rᶜ T₀
... | [4] ⟨G⟩C z Γ₀ t (R≈ , fresh-z , T≡) rewrite T≡ =
  let
    ⟨ G ⟩ C = ⟨G⟩C
    toSpend = persistentDeposits G
    vs      = map select₂ toSpend
    xs      = map select₃ toSpend
    v       = sum vs

    Γ′ = ⟨ C , v ⟩at z ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [4] R≈ ∃Γ≈ fresh-z)
{-
... | [6] c i ds ss v y p c′ y′ Γ₀ t (t≡ , d≡ , R≈ , fresh-y′ , p⟦Δ⟧≡ , As≡∅ , refl) =
  let
    (_ , vs , _) = unzip₃ ds
    (_ , as , _) = unzip₃ ss
    Δ  = || map (uncurry₃ _∶_♯_) ss
    Γ₂ = Δ ∣ Γ₀

    Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [6] t≡ d≡ R≈ ∃Γ≈ fresh-y′ p⟦Δ⟧≡ As≡∅)
... | [8] c i vcis y Γ₀ t (t≡ , d≡ , R≈ , fresh-xs , As≡∅ , refl) =
  let
    Γ′ = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [8] t≡ d≡ R≈ fresh-xs As≡∅ ∃Γ≈)
... | [9] c i v y A x Γ₀ t (d≡ , R≈ , frsg-x , As≡∅ , ∀≤t , refl) =
  let
    Γ′ = ⟨ A has v ⟩at x ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [9] d≡ R≈ ∃Γ≈ frsg-x As≡∅ ∀≤t)
... | [11] A v x v′ x′ y Γ₀ t (R≈ , fresh-y , refl) =
  let
    Γ′ = ⟨ A has (v + v′) ⟩at y ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [11] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y)
... | [13] A v v′ x y y′ Γ₀ t (R≈ , fresh-ys , refl) =
  let
    Γ′ = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [13] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-ys)
... | [15] A v x B′ y Γ₀ t (R≈ , fresh-y , refl) =
  let
    Γ′ = ⟨ B′ has v ⟩at y ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [15] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y)
... | [17] ds j y Γ₀ t i (R≈ , T , ⊆ins , ¬coh , refl) =
  let
    Γ′ = Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([R] [17] {j = j} R≈ ∃Γ≈ T ⊆ins ¬coh)
-}
... | FAIL ins♯ = -, 𝕣∗ , step₂ Rˢ~Rᶜ ([1] ins♯)
