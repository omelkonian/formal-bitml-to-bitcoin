{-# OPTIONS --no-forcing #-}
open import Prelude.Init
  renaming (toWitness to _¡)
  hiding (T)
open SetAsType
open L.Mem
open L.All using (lookup; ¬Any⇒All¬)
open L.Any using (satisfied; lookup-index)
open import Prelude.Lists.Core
open import Prelude.Lists.Indexed
open import Prelude.Lists.Collections
open import Prelude.Lists.Mappings
open import Prelude.Lists.Membership
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.Subsets
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Traces
open import Prelude.Null
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Membership.Patterns
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Decidable

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.DecidableCoherence (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
  hiding (d; Γₜ″; G; C)
  renaming (_∶_♯_ to _∶_#_; ⟨_∶_♯_⟩ to ⟨_∶_#_⟩)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (t; t′; `; ∣_∣; n)
open import Compiler ⋯′ η
open import SecureCompilation.ComputationalContracts ⋯′
open import SecureCompilation.Helpers ⋯
open import SecureCompilation.Coherence ⋯

[1]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {⟨G⟩C : Ad} (let open ∣AD ⟨G⟩C)
    (let Γₜ = Γ at t)
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = advertise⦅ ⟨G⟩C ⦆
      Γ′  = ` ⟨G⟩C ∣ Γ
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″  {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′}  (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {vad? : auto∶ ValidAd ⟨G⟩C} (let vad = vad? ¡)
    {hon? : auto∶ Any (_∈ Hon) partG} (let hon = hon? ¡)
    {d⊆?  : auto∶ ⟨G⟩C ⊆⦅ deposits ⦆ Γ}
    (let d⊆ : deposits ⟨G⟩C ⊆ deposits Γ
         d⊆ x = (d⊆? ¡) x)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

      open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈ using (λˢ)

      C =
        let
          txoutΓ = Txout Γ ∋ Txout≈ {Rˢ ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)
          txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
          txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
        in
          encodeAd ⟨G⟩C (txoutG , txoutC)
      λᶜ = A →∗∶ C
    in
    ────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[1]⋯ {R≈? = R≈} _ {Γ≈}{vad}{hon}{d⊆} =
  [1] (R≈ ¡) (-, Γ≈ ¡) (vad ¡) (hon ¡) (d⊆ ¡)

_∈Hon⇒?All-Is-just_ : ∀ A ms → Dec (A ∈ Hon → All (Is-just {A = ℕ}) ms)
A ∈Hon⇒?All-Is-just ms
  with A ∈? Hon
... | no A∉  = yes λ A∈ → ⊥-elim $ A∉ A∈
... | yes A∈
  with all? (M.Any.dec λ _ → yes tt) ms
... | no ¬p = no λ p → ¬p (p A∈)
... | yes p = yes λ _ → p

instance
  Dec-≢-→∗∶ : (∀ A → λᶜ ≢ A →∗∶ m) ⁇
  Dec-≢-→∗∶ {λᶜ}{m} .dec
    with λᶜ in eq
  ... | submit _ = yes λ _ ()
  ... | delay _  = yes λ _ ()
  ... | _ →O∶ _  = yes λ _ ()
  ... | O→ _ ∶ _ = yes λ _ ()
  ... | A →∗∶ m′
    with m ≟ m′
  ... | yes refl = no λ ¬eq → ¬eq A refl
  ... | no m≢    = yes λ where _ refl → m≢ refl

  Dec-CheckOracle : ∀ {os} → CheckInteractions os ⁇¹
  Dec-CheckOracle {os} {x} .dec
    with x
  ... | _ , nothing , hᵢ = hᵢ ∉? map select₃ (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ select₂) os)
  ... | _ , just Nᵢ , hᵢ
    with ¿ Any (λ (_ , m , h) → (h ≡ hᵢ) × (∣ m ∣ᵐ ≡ η + Nᵢ)) os ¿
  ... | no  x∉ = no λ (_ , _ , x∈ , m≡) → L.All.lookup (¬Any⇒All¬ os x∉) x∈ (refl , m≡)
  ... | yes x∈
    with L.Any.lookup x∈ | ∈-lookup {xs = os} (L.Any.index x∈) | lookup-index x∈
  ... | A , m , _ | x∈ | refl , q = yes (A , m , x∈ , q)

[2]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {⟨G⟩C} (open ∣AD ⟨G⟩C)
    {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
    (let h̅ = map select₃ Δ×h̅
         Δ = map drop₃   Δ×h̅
         (as , ms) = unzip Δ)
    {k⃗ : 𝕂²′ ⟨G⟩C} (let k̅ = concatMap (map pub ∘ codom) $ codom k⃗)
  → let
      Γ = ` ⟨G⟩C ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      R≈  = R≈? ¡

      Δᶜ = || map (uncurry ⟨ A ∶_#_⟩) Δ

      C      = encodeAd ⟨G⟩C (ad∈⇒Txout {⟨G⟩C}{Γ}{Rˢ} 𝟘 R≈ txout′)
      C,h̅,k̅  = encode (C , h̅ , k̅)
      C,h̅,k̅ₐ = SIG (K A) C,h̅,k̅

      α   = auth-commit⦅ A , ⟨G⟩C , Δ ⦆
      Γ′  = Γ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
      t′  = t
      Γₜ′ = Γ′ at t′
      λᶜ  = B →∗∶ C,h̅,k̅ₐ
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , (Γ≈? ¡))
    {as≡?  : auto∶ as ≡ secretsOfᵖ A G} (let as≡  = as≡? ¡)
    {All∉? : auto∶ All (_∉ secretsOfᶜᶠ A Γ₀) as} (let All∉ = All∉? ¡)
    {Hon⇒? : True $ A ∈Hon⇒?All-Is-just ms} (let Hon⇒ = Hon⇒? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([C-AuthCommit] as≡ All∉ Hon⇒) refl

      sechash⁺ : as ↦ ℤ
      sechash⁺ a∈ =
        let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
            (_ , _ , z) , _ = ∈-map⁻ drop₃ a×m∈
        in z

      open H₂ {Rˢ} 𝕣 t α t′ Γ R≈ A A ⟨G⟩C Δ sechash⁺ k⃗ Γ→Γ′ ∃Γ≈ using (λˢ)
    in
  ∀ B {B∈? : auto∶ (B →∗∶ C) ∈ toList Rᶜ} (let B∈ = B∈? ¡)
    {_ : auto∶ All (λ l → ∀ X → l ≢ X →∗∶ C) (Any-tail B∈)}
    {_ : auto∶ All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅}
    {_ : auto∶ All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front B∈)}
    {_ : auto∶ CheckOracleInteractions Rᶜ Δ×h̅}
    {_ : auto∶ Unique h̅}
    {_ : auto∶ Disjoint h̅ (codom sechash′)} →
    ────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[2]⋯ {R≈? = R≈} _ {Γ≈}{as≡}{All∉}{Hon⇒} B {B∈} {p₁} {p₂} {p₃} {p₄} {p₅} {p₆} =
  [2] (R≈ ¡) (-, Γ≈ ¡) (as≡ ¡) (All∉ ¡) (Hon⇒ ¡) (-, B∈ ¡)
             (p₁ ¡) (p₂ ¡) (p₃ ¡) (p₄ ¡) (p₅ ¡) (p₆ ¡)

[3]⋯ :
  ∀ {Γ₀}{t}{A}{x}{v}{B}{Rᶜ}
    {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {⟨G⟩C} (let open ∣AD ⟨G⟩C)

  → let
      Γ = ` ⟨G⟩C ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-init⦅ A , ⟨G⟩C , x ⦆
      Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {p₁ : auto∶ partG ⊆′ committedParticipants ⟨G⟩C Γ₀}
    (let committedA = (p₁ ¡) .unmk⊆)
    {p₂ : auto∶ (A , v , x) ∈ persistentDeposits G} (let A∈per = p₂ ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

      open H₃ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x R≈ Γ→Γ′ ∃Γ≈ committedA using (λˢ; T)

      m = SIG (K̂ A) T
      λᶜ = B →∗∶ m
    in
  ∀ B {p₃ : auto∶ (B →∗∶ (T ♯)) ∈ toList Rᶜ}
    (let ∃B = (∃ λ B → (B →∗∶ (T ♯)) ∈ toList Rᶜ) ∋ B , (p₃ ¡))
    {p₄ : auto∶ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃B .proj₂)} →
    -- (let B∈ = p₃ ¡)
    -- {p₄ : auto∶ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front B∈)} →
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[3]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {R≈? = R≈} Γ″ {Γ≈}{p₁}{p₂} ∃B {p₃}{p₄} =
  [3] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (R≈ ¡) (Γ″ , Γ≈ ¡) ((p₁ ¡) .unmk⊆) (p₂ ¡) (∃B , p₃ ¡) (p₄ ¡)

[4]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {⟨G⟩C} (let open ∣AD ⟨G⟩C)
  → let
      toSpend = persistentDeposits G
      vs      = map select₂ toSpend
      xs      = map select₃ toSpend
      v       = sum vs

      Γ = ` ⟨G⟩C ∣ Γ₀
        ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ⟨G⟩C ] })
                  toSpend
        ∣ || map (_auth[ ♯▷ ⟨G⟩C ]) partG
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = init⦅ G , C ⦆
      Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-z? : auto∶ z ∉ xs ++ ids Γ₀} (let fresh-z = fresh-z? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([C-Init] fresh-z) refl

      open H₄ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ toSpend v z R≈ Γ→Γ′ ∃Γ≈ using (λˢ; T)

      λᶜ = submit T
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[4]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {R≈? = R≈} Γ″ {Γ≈}{p} =
  [4] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (R≈ ¡) (Γ″ , Γ≈ ¡) (p ¡)

[5]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {i : Index c} (let open ∣SELECT c i)
  → let
      Γ = ⟨ c , v ⟩at x ∣ Γ₀
      Γₜ = Γ at t
    in
    {D≡A:D′? : auto∶ A ∈ authDecorations d} (let D≡A:D′ = D≡A:D′? ¡)
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-control⦅ A , x ▷ d ⦆
      Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

      open H₅ {Rˢ} 𝕣 t α t′ c v x Γ₀ A i R≈ Γ→Γ′ ∃Γ≈ D≡A:D′ using (λˢ; T; pubK)

      λᶜ = B →∗∶ SIGᵖ pubK T
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[5]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {R≈? = R≈} Γ″ {Γ≈} =
  [5] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (R≈ ¡) (Γ″ , Γ≈ ¡)

open import Prelude.Newtype
≫Null : ∀ {A} → Pred₀ (List A)
≫Null = newtype¹ Null
instance Dec-≫Null : ∀ {A} ⦃ _ : DecEq A ⦄ → ≫Null {A} ⁇¹
         Dec-≫Null {x = xs} .dec = mk? (Null? xs)

[6]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {ds : DepositRefs} (let (_ , vs , xs) = unzip₃ ds)
    {ss : List (Participant × Secret × ℕ)} (let (_ , as , _)  = unzip₃ ss)
    {i : Index c} (let open ∣SELECT c i; As , ts = decorations d)
  → let
      -- (i) xs = x₁⋯xₖ
      Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
      Δ   = || map (uncurry₃ _∶_#_) ss
      Γ₂  = Δ ∣ Γ₀
      Γ₁₂ = Γ₁ ∣ Γ₂
      Γ   = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₂)
      Γₜ  = Γ at t
    in
    {t≡? : auto∶ t ≡ maximum t ts} (let t≡ = t≡? ¡)
    {d≡? : auto∶ d ≡⋯∶ put xs &reveal as if p ⇒ c′} (let d≡ = d≡? ¡)
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = put⦅ xs , as , y ⦆
      Γ′  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-y′? : auto∶ y′ ∉ y L.∷ ids Γ₁₂} (let fresh-y′ = fresh-y′? ¡)
    {p⟦Δ⟧≡? : auto∶ ⟦ p ⟧ᵖ Δ ≡ just true} (let p⟦Δ⟧≡ = p⟦Δ⟧≡? ¡)
    {As≡∅? : auto∶ ≫Null As} (let As≡∅ = (As≡∅? ¡) .unmk)
  → let
      ∀≤t : All (_≤ t′) ts
      ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

      put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
      put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡
              ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Timeout] As≡∅ ∀≤t put→ refl

      open H₆ {Rˢ} 𝕣 t α t′ c v y ds ss Γ₂ c′ y′ i p R≈ Γ→Γ′ ∃Γ≈ d≡ using (λˢ; T)

      λᶜ = submit T
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[6]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {t≡? = p₁}{p₂}{R≈} Γ″ {Γ≈}{p₃}{p₄}{p₅} =
  [6] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (R≈ ¡) (p₁ ¡) (p₂ ¡) (Γ″ , Γ≈ ¡) (p₃ ¡) (p₄ ¡) (p₅ ¡)

[7]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
    (let Δ = map drop₃   Δ×h̅
         h̅ = map select₃ Δ×h̅)
    {⟨G⟩C} (let open ∣AD ⟨G⟩C) {k⃗ : 𝕂²′ ⟨G⟩C}
  → let
      Γ = ⟨ A ∶ a # just n ⟩ ∣ Γ₀
      Γₜ = Γ at t
    in
    {m≡ : auto∶ ∣ m ∣ᵐ ≤ η}
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-rev⦅ A , a ⦆
      Γ′  = A ∶ a # n ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] [C-AuthRev] refl

      a∈ : a ∈ secrets Rˢ
      a∈ = namesˡ⦅end⦆⊆ Rˢ
          $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ R≈ .proj₂) 𝟘
    in
  ∀ B {_ : auto∶ (B , m , sechash′ {a} a∈) ∈ oracleInteractionsᶜ Rᶜ}
    {∃α? : auto∶ auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labelsʳ Rˢ}
    (let ∃α : auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labelsʳ Rˢ
         ∃α = ∃α? ¡)
    {_ : auto∶ a ∈ secrets G}
  → let
      open H₇ 𝕣 t α t′ A a n Γ₀ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
      open H₇′ 𝕣 t α t′ Δ h̅ k⃗ ∃α using (C,h̅,k̅)
      λᶜ = B →∗∶ m
    in
  ∀ B′ {B? : auto∶ B′ →∗∶ C,h̅,k̅ ∈ toList Rᶜ} (let ∃B = -, B? ¡)
    {_ : auto∶ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃B .proj₂)} →
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[7]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {m≡ = p₁}{R≈} Γ″ {Γ≈} _ {p₂}{p₃}{p₄} _ {p₅}{p₆} =
  [7] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (p₁ ¡) (R≈ ¡) (Γ″ , Γ≈ ¡) (p₂ ¡) (p₃ ¡) (p₄ ¡) _ (p₅ ¡) (p₆ ¡)

[8]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {i : Index c} (let open ∣SELECT c i; As , ts = decorations d)
    {vcis : VIContracts} (let vs , cs , xs = unzip₃ vcis; v = sum vs)
  → let
      Γ = ⟨ c , v ⟩at y ∣ Γ₀
      Γₜ = Γ at t
    in
    {t≡? : auto∶ t ≡ maximum t ts} (let t≡ = t≡? ¡)
    {d≡? : auto∶ d ≡⋯∶ split (zip vs cs)} (let d≡ = d≡? ¡)
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
    {fresh-xs? : auto∶ All (_∉ y L.∷ ids Γ₀) xs} (let fresh-xs = fresh-xs? ¡)
    {As≡∅? : auto∶ Null As} (let As≡∅ = As≡∅? ¡)
  → let
      α   = split⦅ y ⦆
      Γ′  = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      ∀≤t : All (_≤ t′) ts
      ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

      split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
      split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
            ~: [C-Split] {vcis = vcis} fresh-xs

      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Timeout] As≡∅ ∀≤t split→ refl

      open H₈ {Rˢ} 𝕣 t α t′ c v y Γ₀ i vcis R≈ Γ→Γ′ ∃Γ≈ d≡ using (λˢ; T)

      λᶜ = submit T
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[8]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {t≡? = p₁}{p₂}{R≈}{p₃}{p₄} Γ″ {Γ≈} =
  [8] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (p₁ ¡) (R≈ ¡) (p₂ ¡) (p₃ ¡) (p₄ ¡) (Γ″ , Γ≈ ¡)

[9]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {i : Index c} (let open ∣SELECT c i; As , ts = decorations d)
  → let
      Γ = ⟨ c , v ⟩at y ∣ Γ₀
      Γₜ = Γ at t
    in
    {d≡? : auto∶ d ≡⋯∶ withdraw A} (let d≡ = d≡? ¡)
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = withdraw⦅ A , v , y ⦆
      Γ′  = ⟨ A has v ⟩at x ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-x? : auto∶ x ∉ y L.∷ ids Γ₀} (let fresh-x = fresh-x? ¡)
    {As≡∅? : auto∶ ≫Null As} (let As≡∅ = (As≡∅? ¡) .unmk)
    {∀≤t? : auto∶ All (_≤ t) ts} (let ∀≤t = ∀≤t? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Timeout] As≡∅ ∀≤t
        (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x)
        refl

      open H₉ {Rˢ} 𝕣 t α t′ c v y Γ₀ A x i R≈ Γ→Γ′ ∃Γ≈ d≡ using (λˢ; T)

      λᶜ = submit T
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[9]⋯ {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} {d≡? = p₁}{R≈} Γ″ {Γ≈}{p₂}{p₃}{p₄} =
  [9] {Rˢ = Rˢ}{𝕣∗}{⟨G⟩C} (p₁ ¡) (R≈ ¡) (Γ″ , Γ≈ ¡) (p₂ ¡) (p₃ ¡) (p₄ ¡)

[10]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
  → let
      Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-join⦅ A , x ↔ x′ ⦆
      Γ′  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] [DEP-AuthJoin] refl

      n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
      n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
    in
  ∀ B T {BT? : auto∶ flip Any (toList Rᶜ) $ λ l →
               (l ≡ B →∗∶ (T ♯))
             × (inputs  T ≡ (hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]))
             × (outputs T ≡ [ (v + v′) redeemable-by K̂ A ])}
    (let ∃B : ∃ λ B → ∃ λ T → flip Any (toList Rᶜ) $ λ l →
              (l ≡ B →∗∶ (T ♯))
            × (inputs  T ≡ (hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]))
            × (outputs T ≡ [ (v + v′) redeemable-by K̂ A ])
         ∃B = B , T , BT? ¡)
  → let
      T : ∃Tx
      T = 2 , 1 , ∃B .proj₂ .proj₁

      m′ = SIG (K̂ A) T
      λᶜ = B →∗∶ m′

      open H₁₀ {Rˢ} 𝕣 t α t′ A v x v′ x′ Γ₀ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    {_ : auto∶ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front $ ∃B .proj₂ .proj₂)} →
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[10]⋯ {Rˢ = Rˢ}{𝕣∗} {R≈? = R≈} Γ″ {Γ≈} B T {p₁}{p₂} =
  [10] {Rˢ = Rˢ}{𝕣∗} (R≈ ¡) (Γ″ , Γ≈ ¡) (B , T , p₁ ¡) (p₂ ¡)

[11]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
  → let
      Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′
        ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = join⦅ x ↔ x′ ⦆
      Γ′  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-y? : auto∶ y ∉ x L.∷ x′ ∷ ids Γ₀}
    (let fresh-y = fresh-y? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([DEP-Join] fresh-y) refl

      n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
      n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

      T : ∃Tx
      T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
        { inputs  = hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]
        ; wit     = wit⊥
        ; relLock = V.replicate 0
        ; outputs = [ (v + v′) redeemable-by K̂ A ]
        ; absLock = 0 }
      λᶜ = submit T

      open H₁₁ {Rˢ} 𝕣 t α t′ A v x v′ x′ y Γ₀ R≈ (T at 0F) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[11]⋯ {Rˢ = Rˢ}{𝕣∗} {R≈? = R≈} Γ″ {Γ≈} {p₁} =
  [11] {Rˢ = Rˢ}{𝕣∗} (R≈ ¡) (Γ″ , Γ≈ ¡) (p₁ ¡)

[12]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
  → let
      Γ = ⟨ A has (v + v′) ⟩at x ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-divide⦅ A , x ▷ v , v′ ⦆
      Γ′  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] [DEP-AuthDivide] refl

      n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
      n⊆  = namesʳ⦅end⦆⊆ Rˢ
          ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
    in
  ∀ B T {BT? : auto∶ flip Any (toList Rᶜ) $ λ l →
               (l ≡ B →∗∶ (T ♯))
             × (inputs  T ≡ [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ])
             × (outputs T ≡ [ v redeemable-by K̂ A ⨾ v′ redeemable-by K̂ A ])}
        (let ∃B = B , T , BT? ¡)
  → let
      T : ∃Tx
      T = 1 , 2 , ∃B .proj₂ .proj₁

      m′ = SIG (K̂ A) T
      λᶜ = B →∗∶ m′

      open H₁₂ {Rˢ} 𝕣 t α t′ A v v′ x Γ₀ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    {_ : auto∶ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front $ ∃B .proj₂ .proj₂)} →
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[12]⋯ {Rˢ = Rˢ}{𝕣∗} {R≈? = R≈} Γ″ {Γ≈} B T {p₁}{p₂} =
  [12] {Rˢ = Rˢ}{𝕣∗} (R≈ ¡) (Γ″ , Γ≈ ¡) (B , T , p₁ ¡) (p₂ ¡)

[13]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
  → let
      Γ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = divide⦅ x ▷ v , v′ ⦆
      Γ′  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-ys? : auto∶ All (_∉ x L.∷ ids Γ₀ ) [ y ⨾ y′ ]}
    (let fresh-ys = fresh-ys? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([DEP-Divide] fresh-ys) refl

      n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
      n⊆ = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

      T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
        { inputs  = [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ]
        ; wit     = wit⊥
        ; relLock = V.replicate 0
        ; outputs = [ v redeemable-by K̂ A ⨾ v′ redeemable-by K̂ A ]
        ; absLock = 0 }
      λᶜ = submit T

      open H₁₃ {Rˢ} 𝕣 t α t′ A v v′ x Γ₀ y y′ R≈ (T at 0F) (T at 1F) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[13]⋯ {Rˢ = Rˢ}{𝕣∗} {R≈? = R≈} Γ″ {Γ≈} {p₁} =
  [13] {Rˢ = Rˢ}{𝕣∗} (R≈ ¡) (Γ″ , Γ≈ ¡) (p₁ ¡)

[14]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
  → let
      Γ = ⟨ A has v ⟩at x ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-donate⦅ A , x ▷ᵈ B′ ⦆
      Γ′  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] [DEP-AuthDonate] refl

      n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
      n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
    in
  ∀ B T {BT? : auto∶ flip Any (toList Rᶜ) $ λ l →
            (l ≡ B →∗∶ (T ♯))
          × (inputs  T ≡ [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ])
          × (outputs T ≡ [ v redeemable-by K̂ B ])}
        (let ∃B = B , T , BT? ¡)
  → let
      T : ∃Tx
      T = 1 , 1 , ∃B .proj₂ .proj₁

      m′ = SIG (K̂ A) T
      λᶜ = B →∗∶ m′

      open H₁₄ {Rˢ} 𝕣 t α t′ A v x Γ₀ B′ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    {_ : auto∶ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front $ ∃B .proj₂ .proj₂)} →
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[14]⋯ {Rˢ = Rˢ}{𝕣∗} {R≈? = R≈} Γ″ {Γ≈} B T {p₁}{p₂} =
  [14] {Rˢ = Rˢ}{𝕣∗} (R≈ ¡) (Γ″ , Γ≈ ¡) (B , T , p₁ ¡) (p₂ ¡)

[15]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
  → let
      Γ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = donate⦅ x ▷ᵈ B′ ⦆
      Γ′  = ⟨ B′ has v ⟩at y ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-y? : auto∶ y ∉ x L.∷ ids Γ₀} (let fresh-y = fresh-y? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([DEP-Donate] fresh-y) refl

      n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
      n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

      -- (iii) submit transaction T
      T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
        { inputs  = [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ]
        ; wit     = wit⊥
        ; relLock = V.replicate 0
        ; outputs = [ v redeemable-by K̂ B′ ]
        ; absLock = 0 }
      λᶜ = submit T

      -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
      open H₁₅ {Rˢ} 𝕣 t α t′ A v x B′ Γ₀ y R≈ (T at 0F) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[15]⋯ {Rˢ = Rˢ}{𝕣∗} {R≈? = R≈} Γ″ {Γ≈} {p₁} =
  [15] {Rˢ = Rˢ}{𝕣∗} (R≈ ¡) (Γ″ , Γ≈ ¡) (p₁ ¡)

instance
  Dec-≁₁₁ : ∀ {λˢ Rˢ λᶜ Rᶜ} {𝕣∗ : ℝ∗ Rˢ} →
    (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
      → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
      → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓)) ⁇
  Dec-≁₁₁ {λˢ}{Rˢ}{λᶜ}{Rᶜ}{𝕣∗} .dec = {!!}

[16]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {ds : DepositRefs} (let k = length ds; xs = map (proj₂ ∘ proj₂) ds)
    {j : Index ds} (let A = (ds ‼ j) .proj₁; j′ = ‼-map {xs = ds} j)
  → let
      Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
      Γ  = Δ ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = auth-destroy⦅ A , xs , j′ ⦆
      Γ′  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
    {fresh-y? : auto∶ y ∉ ids Γ₀} (let fresh-y = fresh-y? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([DEP-AuthDestroy] fresh-y) refl

      open H₁₆ {Rˢ} 𝕣 t α t′ ds Γ₀  j A y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
    in
  ∀ (T : Tx i 0)
    {_ : auto∶ (hashTxⁱ <$> codom xs↦) ⊆′ V.toList (inputs T)}
    B {T∈? : auto∶ (B →∗∶ (T ♯)) ∈ toList Rᶜ} (let T∈ = T∈? ¡)
    (let T∈ = T∈? ¡)
  → let
      m = SIG (K̂ A) T
      λᶜ = B →∗∶ m
    in
    {_ : auto∶ All (λ l → ∀ B → l ≢ B →∗∶ m) (Any-front T∈)}
    {_ : auto∶ ∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
      → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
      → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓)} →
    ──────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓)
[16]⋯ {Rˢ = Rˢ}{𝕣∗}{ds}{j} {R≈? = R≈} Γ″ {Γ≈} {p₁} T {p₂} B {p₃}{p₄}{p₅} =
  [16] {Rˢ = Rˢ}{𝕣∗}{ds}{j} (R≈ ¡) (Γ″ , Γ≈ ¡) (p₁ ¡) T ((p₂ ¡) .unmk⊆) (B , p₃ ¡) (p₄ ¡) (p₅ ¡)

[17]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    {ds : DepositRefs} (let xs = map (proj₂ ∘ proj₂) ds)
    {j : Index ds}
  → let
      Δ  = || flip map (enumerate ds) (λ{ (i , Aᵢ , vᵢ , xᵢ) →
                ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
      Γ  = Δ ∣ Γ₀
      Γₜ = Γ at t
    in
    {R≈? : auto∶ Rˢ ≈⋯ Γₜ} (let R≈ = R≈? ¡)
  → let
      α   = destroy⦅ xs ⦆
      Γ′  = Γ₀
      t′  = t
      Γₜ′ = Γ′ at t′
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ′} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] [DEP-Destroy] refl

      open H₁₇ {Rˢ} 𝕣 t α t′ ds Γ₀ y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
    in
  ∀ (T : Tx i 0)
    {_ : auto∶ (hashTxⁱ <$> codom xs↦) ⊆′ V.toList (inputs T)}
  → let
      λᶜ = submit (_ , _ , T)
    in
    {_ : auto∶ ∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
      → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
      → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓)} →
    ─────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓)
[17]⋯ {Rˢ = Rˢ}{𝕣∗}{ds}{j} {R≈? = R≈} Γ″ {Γ≈} T {p₁}{p₂} =
  [17] {Rˢ = Rˢ}{𝕣∗}{ds}{j} (R≈ ¡) (Γ″ , Γ≈ ¡) T ((p₁ ¡) .unmk⊆) (p₂ ¡)

[18]⋯ :
  ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    (δ>0 : δ > 0)
  → let
      Γₜ@(Γ at t) = Rˢ .end
      α   = delay⦅ δ ⦆
      t′  = t + δ
      Γₜ′ = Γ at t′
      λᶜ  = delay δ
    in
  ∀ Γ″ {Γ≈? : auto∶ Γ″ ≈ᶜ Γ} (let Γₜ″ = Γ″ at t′; ∃Γ≈ = Γ″ , Γ≈? ¡)
  → let
      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Delay] δ>0

      open H₁₈ {Rˢ} 𝕣 t α t′ Γ (≈ᵗ-refl {Γₜ}) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
    ─────────────────────────────────────────────────────────────
    (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
[18]⋯ {Rˢ = Rˢ}{𝕣∗} δ>0 Γ″ {Γ≈} =
  [18] {Rˢ = Rˢ}{𝕣∗} δ>0 (Γ″ , Γ≈ ¡)
