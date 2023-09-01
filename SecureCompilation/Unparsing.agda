---------------------------------------------------
-- Converting symbolic moves to computational ones.
---------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding (T); open SetAsType
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

module SecureCompilation.Unparsing
  (⋯ : ⋯) (let open ⋯ ⋯)
  (A₀ : Participant) -- whose strategy we are currently translating
  where

open import Compiler ⋯′ η
open import SymbolicModel ⋯′ as S
  hiding (Rˢ′; d)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (t; t′; `; ∣_∣; n)
open import Coherence ⋯

unparseMove :
  ∙ Rˢ ~ Rᶜ
  ∙ Rˢ ——[ α ]→ Γₜ
    ─────────────────────────────
    ∃ λ λᶜ → ∃ λ (𝕒 : 𝔸 Rˢ Γₜ) →
      (Γₜ ∷ Rˢ ⊣ 𝕒) ~ (λᶜ ∷ Rᶜ ✓)

unparseMove
  {Rˢ  = record {end = Γ at _}}
  {α   = advertise⦅ ⟨G⟩C ⦆}
  {Γₜ  = Γ′@(` .⟨G⟩C ∣ Γ) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-Advertise] vad hon d⊆) refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L1] mkℍ  {mk {⟨G⟩C}{Γ} vad hon d⊆ (𝕣∗ ⨾≋ Γ′)}
                 {A = A₀})
unparseMove
  {Rˢ = record {end = Γ@(` .⟨G⟩C ∣ Γ₀) at _}}
  {α  = auth-commit⦅ A , ⟨G⟩C , Δ ⦆}
  {Γₜ = Γ′@(.Γ ∣ Δᶜ ∣ .A auth[ ♯▷ .⟨G⟩C ]) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthCommit] as≡ All∉ Hon⇒) refl)
  = {!!}
{- ** T0D0: step (5) of stipulation protocol
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L2] mkℍ {mk {⟨G⟩C}{Γ₀}{t}{A}
                    ? ? as≡ All∉ Hon⇒
                    (𝕣∗ ⨾≋ Γ′)}
                ? ? ? ? ? ? ?)
-}
unparseMove
  {Rˢ = record {end = (` .ad ∣ Γ₀) at _}}
  {α  = auth-init⦅ A , ad , x ⦆}
  {Γₜ = Γ′@(` .ad ∣ .Γ₀ ∣ .A auth[ .x ▷ˢ .ad ]) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthInit] committedA A∈per) refl)
  = {!!}
{- ** T0D0: step (4) of stipulation protocol
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L3] mkℍ {mk {ad}{Γ₀}{t}{A}{x} committedA A∈per
                    (𝕣∗ ⨾≋ Γ′)}
                ? ?)
-}
unparseMove
  {Rˢ  = record {end = (.(` (⟨ G ⟩ C)) ∣ Γ₀ ∣ _ ∣ _) at _}}
  {α   = init⦅ G , C ⦆}
  {Γₜ  = Γ′ at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-Init] fresh-z) refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L4] mkℍ {mk {⟨ G ⟩ C}{Γ₀} fresh-z (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {α   = put⦅ _ , _ , _ ⦆}
  {Γₜ  = Γ′ at _}
  (𝕣∗ , Rˢ~Rᶜ)
  stepₜ@([Timeout] As≡∅ ∀≤t _ refl)
  with  ds , ss , _ , _ , _ , Γ₀ , _ , d≡
     ,  refl , refl , refl , refl , refl , refl
     ,  fresh-z , p≡ ← match-putₜ stepₜ tt
  = -, -, -, step₁ Rˢ~Rᶜ
       ([L6] mkℍ {mk  {Γ₀ = Γ₀} {ds = ds} {ss = ss}
                      (∀≤⇒≡max ∀≤t) d≡ fresh-z p≡ As≡∅
                      (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {Rˢ  = record {end = (⟨ c , v ⟩at .y ∣ Γ₀) at _}}
  {α   = split⦅ y ⦆}
  {Γₜ  = Γ′ at _}
  (𝕣∗ , Rˢ~Rᶜ)
  stepₜ@([Timeout] As≡∅ ∀≤t _ refl)
  with  vcis , _ , _ , d≡
     ,  refl , refl , refl , refl
     ,  fresh-xs ← match-splitₜ stepₜ tt
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L8] mkℍ {mk  {Γ₀ = Γ₀} {vcis = vcis}
                     (∀≤⇒≡max ∀≤t) d≡ fresh-xs As≡∅
                     (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {α  = withdraw⦅ _ , _ , _ ⦆}
  {Γₜ = Γ′ at _}
  (𝕣∗ , Rˢ~Rᶜ)
  stepₜ@([Timeout] As≡∅ ∀≤t _ refl)
  with Γ₀ , x , d≡ , refl , refl , refl , refl , fresh-x ← match-withdrawₜ stepₜ tt
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L9] mkℍ {mk {Γ₀ = Γ₀} d≡ fresh-x As≡∅ ∀≤t (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {Rˢ = record {end = (⟨ .A has v ⟩at .x ∣ ⟨ .A has v′ ⟩at .x′ ∣ Γ₀) at _}}
  {α  = auth-join⦅ A , x ↔ x′ ⦆}
  {Γₜ = Γ′ at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [DEP-AuthJoin] refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L10] mkℍ {mk {Γ₀ = Γ₀} (𝕣∗ ⨾≋ Γ′)}
                 {B = A₀}
                 {!!} {!!})
{-
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
-}
unparseMove
  {Rˢ = record {end = (⟨ c , v ⟩at .x ∣ Γ₀) at _}}
  {α  = auth-control⦅ A , x ▷ d ⦆}
  {Γₜ = Γ′@(⟨ .c , .v ⟩at .x ∣ A auth[ .x ▷ d ] ∣ .Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([C-AuthControl] d≡) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L5] mkℍ {mk {c}{v}{x}{Γ₀} d≡
                    (𝕣∗ ⨾≋ Γ′)}
                {B = A₀}
                {!!} {!!})
unparseMove
  {Rˢ = record {end = (⟨ .A ∶ .a ♯ just n ⟩ ∣ Γ₀) at _}}
  {α  = auth-rev⦅ A , a ⦆}
  {Γₜ = Γ′@(.A ∶ .a ♯ .n ∣ .Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [C-AuthRev] refl) =
  -, -, -, step₁ Rˢ~Rᶜ
      ([L7] mkℍ {mk {ad = {!!}} {Γ₀ = Γ₀} {!!} {!!}
                    (𝕣∗ ⨾≋ Γ′)
                    {!!}}
                {B = A₀}
                {mˢ = {!!}}
                {!!} {!!} {!!} {!!} {!!})
{-
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
-}
unparseMove
  {α = join⦅ _ ↔ _ ⦆}
  {Γ′@(_ ∣ Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  Γ→Γ′@([Action] ([DEP-Join] fresh-y) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L11] mkℍ {mk {Γ₀ = Γ₀} fresh-y
                     (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {Rˢ = record {end = (⟨ .A has .(v + v′) ⟩at .x ∣ Γ₀) at _}}
  {α  = auth-divide⦅ A , x ▷ v , v′ ⦆}
  {Γₜ = Γ′@(⟨ .A has .(v + v′) ⟩at .x ∣ .A auth[ .x ▷⟨ .A , .v , .v′ ⟩ ] ∣ .Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  Γ→Γ′@([Action] [DEP-AuthDivide] refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L12] mkℍ {mk {Γ₀ = Γ₀}
                     (𝕣∗ ⨾≋ Γ′)}
                 {B = A₀}
                 {!!} {!!})
{-
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
-}
unparseMove
  {Rˢ = record {end = (⟨ A has .(v + v′) ⟩at .x ∣ _ ∣ Γ₀) at _}}
  {α  = divide⦅ x ▷ v , v′ ⦆}
  {Γₜ = Γ′ at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Divide] fresh-ys) refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L13] mkℍ {mk {Γ₀ = Γ₀} fresh-ys (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {α  = auth-donate⦅ A , x ▷ᵈ B′ ⦆}
  {Γₜ = Γ′@(_ ∣ _ ∣ Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] [DEP-AuthDonate] refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([L14] mkℍ {mk {Γ₀ = Γ₀} (𝕣∗ ⨾≋ Γ′)}
                 {B = A₀}
                 {!!} {!!})
{-
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
-}
unparseMove
  {Rˢ = record {end = (⟨ A has v ⟩at .x ∣ A auth[ .x ▷ᵈ .B′ ] ∣ Γ₀) at _}}
  {α  = donate⦅ x ▷ᵈ B′ ⦆}
  {Γₜ = Γ′@(⟨ .B′ has .v ⟩at y ∣ .Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Donate] fresh-y) refl) =
    -, -, -, step₁ Rˢ~Rᶜ
      ([L15] mkℍ {mk {Γ₀ = Γ₀} fresh-y
                 (𝕣∗ ⨾≋ Γ′)})
unparseMove
  {Rˢ = record {end = (Δ ∣ Γ₀) at _}}
  {α  = auth-destroy⦅ A , xs , j′ ⦆}
  {Γₜ = Γ′@(.Δ ∣ .A auth[ .xs , .j′ ▷ᵈˢ y ] ∣ .Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-AuthDestroy] {y}{Γ₀}{ds}{j} fresh-y) refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([R16⊣ {!!} ] mkℍ {mk {Γ₀ = Γ₀} {ds = ds}
                         j fresh-y
                         (𝕣∗ ⨾≋ Γ′)}
                     {B = A₀}
                     {!!} {!!})
unparseMove
  {Rˢ = record {end = (_ ∣ Γ₀) at _}}
  {α  = destroy⦅ xs ⦆}
  {Γₜ = Γ′@(.Γ₀) at _}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Action] ([DEP-Destroy] {Γ = Γ₀} {ds = ds}) refl)
  = -, -, -, step₁ Rˢ~Rᶜ
      ([R17⊣ {!!} ]
        mkℍ {mk {Γ₀ = Γ₀} {ds = ds} (𝕣∗ ⨾≋ Γ′)}
            {i = ?}
            {o = ?}
            {!!} {!!})
unparseMove
  {Rˢ = record {end = Γ at t}}
  {α  = delay⦅ δ ⦆}
  {Γₜ = Γ′@.Γ at .(t + δ)}
  (𝕣∗ , Rˢ~Rᶜ)
  ([Delay] δ>0)
  = -, -, -, step₁ Rˢ~Rᶜ ([L18] mkℍ {mk {Γ} δ>0 (𝕣∗ ⨾≋ Γ′)})
unparseMove {α = delay⦅ _ ⦆} _ ([Action] ([C-Control] _ _ _ ()) _)

-- ** n-ary version
unparseMoves : Rˢ ~ Rᶜ → List (∃ λ α → ∃ (Rˢ ——[ α ]→_)) → C.Labels
unparseMoves Rˢ~Rᶜ = map λ where
  (α , Γₜ , R→) → unparseMove Rˢ~Rᶜ R→ .proj₁
