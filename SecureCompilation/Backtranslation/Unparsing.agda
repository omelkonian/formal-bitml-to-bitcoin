---------------------------------------------------
-- Converting symbolic moves to computational ones.
---------------------------------------------------

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
open import Prelude.Nary hiding (⟦_⟧)
open import Prelude.Apartness
open import Prelude.General
open import Prelude.Tactics.Existentials

open import Bitcoin using (KeyPair)
open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Backtranslation.Unparsing
  (⋯ : ⋯) (let open ⋯ : ⋯)
  (A₀ : Participant) -- whose strategy we are currently translating
  where

open import SymbolicModel ⋯′ as S
  hiding (Rˢ′; d)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Initial; Σ; t; t′; `; ∣_∣; n)
open import SecureCompilation.Helpers ⋯
open import SecureCompilation.Coherence ⋯ as SC

unparseMove :
  ∙ Rˢ ~ Rᶜ
  ∙ Rˢ ——[ α ]→ Γₜ
    ─────────────────────────────
    ∃ λ λᶜ → ∃ λ (𝕒 : 𝔸 Rˢ Γₜ) →
      (Γₜ ∷ Rˢ ⊣ 𝕒) ~ (λᶜ ∷ Rᶜ ✓)
unparseMove
  {Rˢ@(record {end = Γₜ@(Γ at t)})}
  {Rᶜ}
  {advertise⦅ ⟨G⟩C ⦆}
  {Γₜ′@(Γ′@(` .⟨G⟩C ∣ .Γ) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-Advertise] vad hon d⊆) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [1] {Γ = Γ} {A = A₀} R≈ ∃Γ≈ vad hon d⊆)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(` .⟨G⟩C ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-commit⦅ A , ⟨G⟩C , Δ ⦆}
  {Γₜ′@(Γ′@(.Γ ∣ Δᶜ ∣ .A auth[ ♯▷ .⟨G⟩C ]) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthCommit] as≡ All∉ Hon⇒) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L] [2] {Γ₀ = Γ₀} {B = {!!}} {Δ×h̅ = {!!}} {k⃗ = {!!}}
      R≈ ∃Γ≈ as≡ All∉ Hon⇒ {!!} {!!} {!!} {!!} {!!})
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(` .ad ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-init⦅ A , ad , x ⦆}
  {Γₜ′@(Γ′@(` .ad ∣ .Γ₀ ∣ .A auth[ .x ▷ˢ .ad ]) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthInit] committedA A∈per) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L] [3] {⟨G⟩C = ad} {Γ₀ = Γ₀} {x = x} {B = {!!}} R≈ ∃Γ≈ committedA A∈per {!!})
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@( .(` (⟨ G ⟩ C)) ∣ Γ₀ ∣ _ ∣ _)
    at t)})}
  {Rᶜ}
  {init⦅ G , C ⦆}
  {Γₜ′@(Γ′@(_) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-Init] fresh-z) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [4] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-z)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ c , v ⟩at .x ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-control⦅ A , x ▷ d ⦆}
  {Γₜ′@(Γ′@(⟨ .c , .v ⟩at .x ∣ A auth[ .x ▷ d ] ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthControl] D≡A:D′) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [5] {Γ₀ = Γ₀} {B = A₀} D≡A:D′ R≈ ∃Γ≈)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(_)
    at t)})}
  {Rᶜ}
  {put⦅ xs , as , y ⦆}
  {Γₜ′@(Γ′@(_) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  stepₜ@([Timeout] As≡∅ ∀≤t _ refl)
  with ds , ss , p , c , v , Γ₀ , z , d≡ , refl , refl , refl , refl , refl , refl
     , fresh-z , p≡
     ← match-putₜ stepₜ tt =
  let
    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L] [6] {Γ₀ = Γ₀} {ds = ds}{ss}
               (∀≤⇒≡max ∀≤t) d≡ (refl , ↭-refl) ∃Γ≈ fresh-z p≡ As≡∅)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ .A ∶ .a ♯ just n ⟩ ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-rev⦅ A , a ⦆}
  {Γₜ′@(Γ′@(.A ∶ .a ♯ .n ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [C-AuthRev] refl) =
  -, -, -, step₁ Rˢ~Rᶜ ([L] [7] {Γ₀ = Γ₀} {B = A₀} m≤ R≈ ∃Γ≈ ∃B ∃α a∈G ∃λ first-λᶜ)
  where
    postulate
      _m : Message
      m≤ : ∣ _m ∣ᵐ ≤ η
      Δ×h̅ : List (Secret × Maybe ℕ × ℤ)
      ⟨G⟩C : Ad
      k⃗ : 𝕂²′ ⟨G⟩C

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

    a∈ : a ∈ namesˡ Rˢ
    a∈ = namesˡ⦅end⦆⊆ Rˢ
       $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈) (here refl)

    _Δ : List (Secret × Maybe ℕ)
    _Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

    _C : Message
    _C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

    h̅ : Message
    h̅ = map (proj₂ ∘ proj₂) Δ×h̅

    k̅ : Message
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ : Message
    C,h̅,k̅ = _C ◇ h̅ ◇ k̅

    postulate
      ∃B : ∃ λ B → (B , _m , [ sechash′ {a} a∈ ]) ∈ oracleInteractionsᶜ Rᶜ
      ∃α : auth-commit⦅ A , ⟨G⟩C , _Δ ⦆ ∈ labels Rˢ
      a∈G : a ∈ namesˡ (⟨G⟩C .G)

      ∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) (toList Rᶜ)
      first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ _m) (Any-tail ∃λ)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ c , v ⟩at .y ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {split⦅ y ⦆}
  {Γₜ′@(Γ′@(_) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  stepₜ@([Timeout] As≡∅ ∀≤t _ refl)
  with vcis , Γ₀ , y , d≡ , refl , refl , refl , refl , fresh-xs ← match-splitₜ stepₜ tt =
  let
    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L] [8] {vcis = vcis} {Γ₀ = Γ₀}
           (∀≤⇒≡max ∀≤t) d≡ (refl , ↭-refl) fresh-xs As≡∅ ∃Γ≈)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(_)
    at t)})}
  {Rᶜ}
  {withdraw⦅ A , v , y ⦆}
  {Γₜ′@(Γ′@(_) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  stepₜ@([Timeout] As≡∅ ∀≤t _ refl)
  with Γ₀ , x , d≡ , refl , refl , refl , refl , fresh-x ← match-withdrawₜ stepₜ tt =
  let
    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [9] {Γ₀ = Γ₀} d≡ (refl , ↭-refl) ∃Γ≈ fresh-x As≡∅ ∀≤t)
unparseMove
  {Rˢ@(record {end = Γₜ@(Γ@(⟨ A has v ⟩at .x ∣ ⟨ A has v′ ⟩at .x′ ∣ Γ₀) at t)})}
  {Rᶜ}
  {auth-join⦅ A , x ↔ x′ ⦆}
  {Γₜ′@(Γ′@(⟨ .A has .v ⟩at .x ∣ ⟨ .A has .v′ ⟩at .x′ ∣ .A auth[ .x ↔ .x′ ▷⟨ .A , .(v + v′) ⟩ ] ∣ Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [DEP-AuthJoin] refl) =
  let
    𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
    n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
    x∈  = n⊆ (here refl)
    x∈′ = n⊆ (there $′ here refl)

    ∃λ : Any (λ l → ∃ λ B → ∃ λ T
         → (l ≡ B →∗∶ [ T ♯ ])
         × (inputs  T ≡ hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ [])
         × (outputs T ≡ [ 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
         ) (toList Rᶜ)
    ∃λ = {!!}

    T : ∃Tx
    T = 2 , 1 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

    m′ = [ SIG (K̂ A) T ]

    first-λᶜ : All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
    first-λᶜ = {!!}
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [10] {Γ₀ = Γ₀} {B = {!!}} R≈ ∃Γ≈ ∃λ first-λᶜ)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ .A auth[ .x ↔ .x′ ▷⟨ .A , .(v + v′) ⟩ ] ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {α@(join⦅ x ↔ x′ ⦆)}
  {Γₜ′@(Γ′@(⟨ .A has .(v + v′) ⟩at y ∣ .Γ₀) at t′@(.t))}
  (𝕣∗ , Rˢ~Rᶜ)
  Γ→Γ′@([Action] ([DEP-Join] fresh-y) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [11] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y)
unparseMove
  {Rˢ@(record {end = Γₜ@(Γ@(⟨ .A has .(v + v′) ⟩at .x ∣ Γ₀) at t)})}
  {Rᶜ}
  {auth-divide⦅ A , x ▷ v , v′ ⦆}
  {Γₜ′@(Γ′@(⟨ .A has .(v + v′) ⟩at .x ∣ .A auth[ .x ▷⟨ .A , .v , .v′ ⟩ ] ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  Γ→Γ′@([Action] [DEP-AuthDivide] refl) =
  let
    𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
    n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
    x∈  = n⊆ (here refl)

    ∃λ : Any (λ l → ∃ λ B → ∃ λ T
         → (l ≡ B →∗∶ [ T ♯ ])
         × (inputs  T ≡ [ hashTxⁱ (txout′ {x} x∈) ])
         × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
         ) (toList Rᶜ)
    ∃λ = {!!}

    T : ∃Tx
    T = 1 , 2 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

    m′ = [ SIG (K̂ A) T ]

    first-λᶜ : All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
    first-λᶜ = {!!}
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [12] {Γ₀ = Γ₀} {B = {!!}} R≈ ∃Γ≈ ∃λ first-λᶜ)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ A has .(v + v′) ⟩at .x ∣ .A auth[ .x ▷⟨ .A , .v , .v′ ⟩ ] ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {divide⦅ x ▷ v , v′ ⦆}
  {Γₜ′@(Γ′@(⟨ .A has .v ⟩at y ∣ ⟨ .A has .v′ ⟩at y′ ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Divide] fresh-ys) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [13] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-ys)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ .A has v ⟩at .x ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-donate⦅ A , x ▷ᵈ B′ ⦆}
  {Γₜ′@(Γ′@(⟨ .A has .v ⟩at .x ∣ .A auth[ .x ▷ᵈ .B′ ] ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [DEP-AuthDonate] refl) =
  let
    𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
    n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
    x∈  = n⊆ (here refl)

    ∃λ : Any (λ l → ∃ λ B → ∃ λ T
             → (l ≡ B →∗∶ [ T ♯ ])
             × (inputs  T ≡ [ hashTxⁱ (txout′ {x} x∈) ])
             × (outputs T ≡ [ v -redeemableWith- K̂ B′ ])
             ) (toList Rᶜ)
    ∃λ = {!!}

    T : ∃Tx
    T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

    m′ = [ SIG (K̂ A) T ]

    first-λᶜ : All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
    first-λᶜ = {!!}
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [14] {Γ₀ = Γ₀} {B = {!!}} R≈ ∃Γ≈ ∃λ first-λᶜ)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ A has v ⟩at .x ∣ A auth[ .x ▷ᵈ .B′ ] ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {donate⦅ x ▷ᵈ B′ ⦆}
  {Γₜ′@(Γ′@(⟨ .B′ has .v ⟩at y ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Donate] fresh-y) refl) =
  let
    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [15] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(Δ ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-destroy⦅ A , xs , j′ ⦆}
  {Γₜ′@(Γ′@(.Δ ∣ .A auth[ .xs , .j′ ▷ᵈˢ y ] ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-AuthDestroy] {y}{Γ₀}{ds}{j} fresh-y) refl) =
  let
    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([R] [16] {Γ₀ = Γ₀} {i = {!!}} {B = A₀} {ds = ds}
                (refl , ↭-refl) ∃Γ≈ fresh-y
                {!!} {!!} {!!} {!!} {!!})
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(_ ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {destroy⦅ xs ⦆}
  {Γₜ′@(Γ′@(.Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Destroy] {y = y} {Γ = Γ₀} {ds = ds}) refl) =
  let
    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([R] [17] {Γ₀ = Γ₀} {i = {!!}} {ds = ds} {j = {!!}}
                (refl , ↭-refl) ∃Γ≈
                {!!} {!!} {!!})

unparseMove
  {Rˢ@(record {end = Γₜ@(Γ at t)})}
  {Rᶜ}
  {delay⦅ δ ⦆}
  {Γₜ′@(Γ′@.Γ at .(t + δ))}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Delay] δ>0) =
  let
    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ ([L] [18] δ>0 ∃Γ≈)
unparseMove {α = delay⦅ _ ⦆} _ ([Action] ([C-Control] _ _ _ ()) _)

unparseMoves : Rˢ ~ Rᶜ → List (∃ λ α → ∃ (Rˢ ——[ α ]→_)) → C.Labels
unparseMoves Rˢ~Rᶜ = map λ where
  (α , Γₜ , R→) → unparseMove Rˢ~Rᶜ R→ .proj₁
