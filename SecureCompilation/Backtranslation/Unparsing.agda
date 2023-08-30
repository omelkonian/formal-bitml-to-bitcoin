---------------------------------------------------
-- Converting symbolic moves to computational ones.
---------------------------------------------------

-- {-# OPTIONS --allow-unsolved-metas #-}
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
open import Prelude.General

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Backtranslation.Unparsing
  (⋯ : ⋯) (let open ⋯ ⋯)
  (A₀ : Participant) -- whose strategy we are currently translating
  where

open import Compiler ⋯′ η
open import SymbolicModel ⋯′ as S
  hiding (Rˢ′; d)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Σ; t; t′; `; ∣_∣; n)
open import Coherence ⋯

postulate
  unparseMove :
    ∙ Rˢ ~ Rᶜ
    ∙ Rˢ ——[ α ]→ Γₜ
      ─────────────────────────────
      ∃ λ λᶜ → ∃ λ (𝕒 : 𝔸 Rˢ Γₜ) →
        (Γₜ ∷ Rˢ ⊣ 𝕒) ~ (λᶜ ∷ Rᶜ ✓)
-- ** too slow
{-
unparseMove
  {Rˢ@(record {end = Γₜ@(Γ at t)})}
  {Rᶜ}
  {advertise⦅ ⟨G⟩C ⦆}
  {Γₜ′@(Γ′@(` .⟨G⟩C ∣ .Γ) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-Advertise] vad hon d⊆) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L1] mkℍ {mk {⟨G⟩C}{Γ}{t} vad hon d⊆
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                {A = ?})
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

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L2] mkℍ {mk {⟨G⟩C}{Γ₀}{t}{A} ? ? as≡ All∉ Hon⇒
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                ? ? ? ? ? ? ?)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(` .ad ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-init⦅ A , ad , x ⦆}
  {Γₜ′@(Γ′@(` .ad ∣ .Γ₀ ∣ .A auth[ .x ▷ˢ .ad ]) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthInit] committedA A∈per) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L3] mkℍ {mk {ad}{Γ₀}{t}{A}{x} committedA A∈per
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                ? ?)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@( .(` (⟨ G ⟩ C)) ∣ Γ₀ ∣ _ ∣ _)
    at t)})}
  {Rᶜ}
  {init⦅ G , C ⦆}
  {Γₜ′@(Γ′@(_) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-Init] fresh-z) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L4] mkℍ {mk {⟨ G ⟩ C}{Γ₀}{t} fresh-z
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ c , v ⟩at .x ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-control⦅ A , x ▷ d ⦆}
  {Γₜ′@(Γ′@(⟨ .c , .v ⟩at .x ∣ A auth[ .x ▷ d ] ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthControl] d≡) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L5] mkℍ {mk {c}{v}{x}{Γ₀}{t}{A}{i = ?} d≡
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                ? ?)
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
    -, -, -, step₁ Rˢ~Rᶜ
      ([L6] mkℍ {mk {_}{v}{y}{c}{z}{Γ₀ = Γ₀}{_}{p}{ds}{ss}{i = ?}
                    (∀≤⇒≡max ∀≤t) d≡ fresh-z p≡ As≡∅
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ .A ∶ .a ♯ just n ⟩ ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-rev⦅ A , a ⦆}
  {Γₜ′@(Γ′@(.A ∶ .a ♯ .n ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [C-AuthRev] refl) =
  -, -, -, step₁ Rˢ~Rᶜ
      ([L7] mkℍ {mk {ad = ?}{A}{a}{n}{Γ₀}{t} ? ?
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)
                    ?}
                ? ? ? ? ?)
  -- ([L] [7] {Γ₀ = Γ₀} {B = A₀} m≤ R≈ ∃Γ≈ ∃B ∃α a∈G ∃λ first-λᶜ)
  where
    postulate
      _m : Message
      m≤ : ∣ _m ∣ᵐ ≤ η
      Δ×h̅ : List (Secret × Maybe ℕ × ℤ)
      ⟨G⟩C : Ad
      k⃗ : 𝕂²′ ⟨G⟩C

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

    a∈ : a ∈ namesˡ Rˢ
    a∈ = namesˡ⦅end⦆⊆ Rˢ
       $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈) (here refl)

    _Δ : List (Secret × Maybe ℕ)
    _Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

    _C : Message
    _C = encodeAd ⟨G⟩C {!!} -- (txoutG , txoutC)

    -- h̅ : Message
    -- h̅ = map (proj₂ ∘ proj₂) Δ×h̅

    -- k̅ : Message
    -- k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    -- C,h̅,k̅ : Message
    -- C,h̅,k̅ = _C ◇ h̅ ◇ k̅

    -- postulate
    --   ∃B : ∃ λ B → (B , _m , [ sechash′ {a} a∈ ]) ∈ oracleInteractionsᶜ Rᶜ
    --   ∃α : auth-commit⦅ A , ⟨G⟩C , _Δ ⦆ ∈ labels Rˢ
    --   a∈G : a ∈ namesˡ (⟨G⟩C .G)

    --   ∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) (toList Rᶜ)
    --   first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ _m) (Any-tail ∃λ)
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
    -, -, -, step₁ Rˢ~Rᶜ
      ([L8] mkℍ {mk {c}{y}{Γ₀}{i = ?}{vcis} (∀≤⇒≡max ∀≤t) d≡ fresh-xs As≡∅
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
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
    -, -, -, step₁ Rˢ~Rᶜ
      ([L9] mkℍ {mk {Γ₀ = Γ₀} d≡ fresh-x As≡∅ ∀≤t
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
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

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
    n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
    x∈  = n⊆ (here refl)
    x∈′ = n⊆ (there $′ here refl)

    -- ∃λ : Any (λ l → ∃ λ B → ∃ λ T
    --      → (l ≡ B →∗∶ [ T ♯ ])
    --      × (inputs  T ≡ hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ [])
    --      × (outputs T ≡ [ 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
    --      ) (toList Rᶜ)
    -- ∃λ = {!!}

    -- T : ∃Tx
    -- T = 2 , 1 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

    -- m′ = [ SIG (K̂ A) T ]

    -- first-λᶜ : All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
    -- first-λᶜ = {!!}
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L10] mkℍ {mk {Γ₀ = Γ₀}
                     (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                 ? ?)
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

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L11] mkℍ {mk {Γ₀ = Γ₀} fresh-y
                     (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
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

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
    n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
    x∈  = n⊆ (here refl)

    -- ∃λ : Any (λ l → ∃ λ B → ∃ λ T
    --      → (l ≡ B →∗∶ [ T ♯ ])
    --      × (inputs  T ≡ [ hashTxⁱ (txout′ {x} x∈) ])
    --      × (outputs T ≡ (v redeemable-by K̂ A) ∷ (v′ redeemable-by K̂ A) ∷ [])
    --      ) (toList Rᶜ)
    -- ∃λ = {!!}

    -- T : ∃Tx
    -- T = 1 , 2 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

    -- m′ = [ SIG (K̂ A) T ]

    -- first-λᶜ : All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
    -- first-λᶜ = {!!}
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L12] mkℍ {mk {Γ₀ = Γ₀}
                    (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                ? ?)
 -- ([L] [12] {Γ₀ = Γ₀} {B = {!!}} R≈ ∃Γ≈ ∃λ first-λᶜ)
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(⟨ A has .(v + v′) ⟩at .x ∣ .A auth[ .x ▷⟨ .A , .v , .v′ ⟩ ] ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {divide⦅ x ▷ v , v′ ⦆}
  {Γₜ′@(Γ′@(⟨ .A has .v ⟩at y ∣ ⟨ .A has .v′ ⟩at y′ ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Divide] fresh-ys) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L13] mkℍ {mk {Γ₀ = Γ₀} fresh-ys (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
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

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl

    n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
    n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
    x∈  = n⊆ (here refl)

    -- ∃λ : Any (λ l → ∃ λ B → ∃ λ T
    --          → (l ≡ B →∗∶ [ T ♯ ])
    --          × (inputs  T ≡ [ hashTxⁱ (txout′ {x} x∈) ])
    --          × (outputs T ≡ [ v redeemable-by K̂ B′ ])
    --          ) (toList Rᶜ)
    -- ∃λ = {!!}

    -- T : ∃Tx
    -- T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

    -- m′ = [ SIG (K̂ A) T ]

    -- first-λᶜ : All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
    -- first-λᶜ = {!!}
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L14] mkℍ {mk {Γ₀ = Γ₀} (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                 ? ?)
    -- ([L] [14] {Γ₀ = Γ₀} {B = {!!}} R≈ ∃Γ≈ ∃λ first-λᶜ)
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

    ∃Γ≈ : ∃ (_≈ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, -, step₁ Rˢ~Rᶜ
      ([L15] mkℍ {mk {Γ₀ = Γ₀} fresh-y
                 (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
-- ** unification errors for `destroy` actions, T0D0: fording view
{-
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(Δ ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {auth-destroy⦅ A , xs , j′ ⦆}
  {Γₜ′@(Γ′@(.Δ ∣ .A auth[ .xs , .j′ ▷ᵈˢ y ] ∣ .Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-AuthDestroy] {y}{Γ₀}{ds}{j} fresh-y) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([R16⊣ ? ] mkℍ {mk {y}{Γ₀}{t}{ds} j fresh-y
                         (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
                     ? ?)
      -- {Γ₀ = Γ₀} {i = {!!}} {B = A₀} {ds = ds}
unparseMove
  {Rˢ@(record {end = Γₜ@(
    Γ@(_ ∣ Γ₀)
    at t)})}
  {Rᶜ}
  {destroy⦅ xs ⦆}
  {Γₜ′@(Γ′@(.Γ₀) at .t)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Destroy] {y = y} {Γ = Γ₀} {ds = ds}) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([R17⊣ {!!} ]
        mkℍ {mk {Γ₀}{y}{t}{ds} (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)}
            {!!} {!!})
-}
unparseMove
  {Rˢ@(record {end = Γₜ@(Γ at t)})}
  {Rᶜ}
  {delay⦅ δ ⦆}
  {Γₜ′@(Γ′@.Γ at .(t + δ))}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Delay] δ>0) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L18] mkℍ {mk {Γ} δ>0 (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Γ′ ⊣ ↭-refl)})
-- ** unification errors for `C-Control` rules, T0D0: fording view
-- unparseMove {α = delay⦅ _ ⦆} _ ([Action] ([C-Control] _ _ _ ()) _)
-}
unparseMoves : Rˢ ~ Rᶜ → List (∃ λ α → ∃ (Rˢ ——[ α ]→_)) → C.Labels
unparseMoves Rˢ~Rᶜ = map λ where
  (α , Γₜ , R→) → unparseMove Rˢ~Rᶜ R→ .proj₁
