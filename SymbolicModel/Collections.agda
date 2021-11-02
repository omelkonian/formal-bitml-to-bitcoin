------------------------------------------------------------------------
-- Collecting elements out of symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.General
open import Prelude.DecLists

open import Bitcoin.Crypto
open import Bitcoin.Tx

module SymbolicModel.Collections
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
  hiding ( _∎; begin_)

private variable X : Set

instance
  HXʳ : ⦃ ∀ {Γₜ Γₜ′} → (Γₜ —↠ₜ Γₜ′) has X ⦄ → Run has X
  HXʳ ⦃ h ⦄ .collect = collect ⦃ h ⦄ ∘ trace

-- [BUG] instantiated `advertisements ⦃ HAʳ ⦄`, to aid Agda's type inference
authorizedHonAdsʳ : Run → List Advertisement
authorizedHonAdsʳ = collect

ads⦅end⦆⊆ : ∀ R → advertisements (R .end) ⊆ advertisements R
ads⦅end⦆⊆ R
  = ⊆-concatMap⁺
  $ L.Mem.∈-map⁺ advertisements
  $ L.Mem.∈-map⁺ cfg
  $ end∈allCfgsᵗ {R}

names⦅end⦆⊆ : ∀ R → names (R .end) ⊆ names R
names⦅end⦆⊆ R
  = ⊆-concatMap⁺
  $ L.Mem.∈-map⁺ names
  $ L.Mem.∈-map⁺ cfg
  $ end∈allCfgsᵗ {R}

namesˡ⦅end⦆⊆ : ∀ (R : Run) → namesˡ (R .end) ⊆ namesˡ R
namesˡ⦅end⦆⊆ = mapMaybe-⊆ isInj₁ ∘ names⦅end⦆⊆

namesʳ⦅end⦆⊆ : ∀ (R : Run) → namesʳ (R .end) ⊆ namesʳ R
namesʳ⦅end⦆⊆ = mapMaybe-⊆ isInj₂ ∘ names⦅end⦆⊆

ads-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ advertisements R ++ advertisements (cfg Γₜ)
ads-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq =
  begin
    advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    concatMap authorizedHonAds (allCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (concatMap authorizedHonAds) (allCfgs≡ {R = R} Γ← eq) ⟩
    concatMap authorizedHonAds (allCfgs R ∷ʳ cfg Γₜ)
  ≡⟨ concatMap-++ authorizedHonAds (allCfgs R) [ cfg Γₜ ] ⟩
    concatMap authorizedHonAds (allCfgs R) ++ concatMap authorizedHonAds [ cfg Γₜ ]
  ≡⟨⟩
    advertisements R ++ concatMap authorizedHonAds [ cfg Γₜ ]
  ≡⟨ cong (advertisements R ++_) (L.++-identityʳ _) ⟩
    advertisements R ++ authorizedHonAds (cfg Γₜ)
  ∎
  where open ≡-Reasoning

names-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → names (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ names R ++ names Γₜ
names-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq =
  begin
    names (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    concatMap collect (allCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (concatMap collect) (allCfgs≡ {R = R} Γ← eq) ⟩
    concatMap collect (allCfgs R ∷ʳ cfg Γₜ)
  ≡⟨ concatMap-++ collect (allCfgs R) [ cfg Γₜ ] ⟩
    concatMap collect (allCfgs R) ++ concatMap collect [ cfg Γₜ ]
  ≡⟨⟩
    names R ++ concatMap collect [ cfg Γₜ ]
  ≡⟨ cong (names R ++_) (L.++-identityʳ _) ⟩
    names R ++ collect (cfg Γₜ)
  ∎
  where open ≡-Reasoning

namesˡ-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → namesˡ (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ namesˡ R ++ namesˡ Γₜ
namesˡ-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq
  rewrite names-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq = mapMaybe-++ isInj₁ (names R) (names Γₜ)

namesʳ-←—— : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → namesʳ (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ namesʳ R ++ namesʳ Γₜ
namesʳ-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq
  rewrite names-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq = mapMaybe-++ isInj₂ (names R) (names Γₜ)

names-∎ : ∀ {init : Initial Γ₀}
  → names ((Γ₀ at 0) ∎⊣ (init , refl))
  ≡ names Γ₀
names-∎ = L.++-identityʳ _

namesˡ-∎ : ∀ {init : Initial Γ₀}
  → namesˡ ((Γ₀ at 0) ∎⊣ (init , refl))
  ≡ namesˡ Γ₀
namesˡ-∎ {Γ₀}{init} = cong filter₁ $ names-∎ {Γ₀}{init}

namesʳ-∎ : ∀ {init : Initial Γ₀}
  → namesʳ ((Γ₀ at 0) ∎⊣ (init , refl))
  ≡ namesʳ Γ₀
namesʳ-∎ {Γ₀}{init} = cong filter₂ $ names-∎ {Γ₀}{init}

ads∈-⊎ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → ad ∈ advertisements (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  → ad ∈ advertisements R
  ⊎ ad ∈ advertisements Γₜ
ads∈-⊎ {α}{Γₜ′}{Γₜ}{R}{ad}{x} Γ← eq ad∈
  rewrite ads-←—— {α}{Γₜ′}{Γₜ}{R}{x} Γ← eq
  with L.Mem.∈-++⁻ (advertisements R) {advertisements Γₜ} ad∈
... | inj₁ ad∈R  = inj₁ ad∈R
... | inj₂ ad∈Γ′ = inj₂ ad∈Γ′

-- Useful type aliases for maps over specific sets.
Txout : ⦃ X has Name ⦄ → Pred₀ X
Txout x = namesʳ x ↦ TxInput′

Sechash : ⦃ X has Name ⦄ → Pred₀ X
Sechash x = namesˡ x ↦ ℤ

𝕂 : Pred₀ Precondition
𝕂 g = nub-participants g ↦ KeyPair

𝕂²′ : Pred₀ Advertisement
𝕂²′ (⟨ g ⟩ c) = subtermsᶜ′ c ↦ nub-participants g ↦ KeyPair

𝕂² : ⦃ X has Advertisement ⦄ → Pred₀ X
𝕂² x = advertisements x ↦′ 𝕂²′

-- [BUG] somehow if we didn't package this constructor arguments in ℝ, we get unification/panic errors!
-- (issue appear at the usage site)
-- ℝ = ∃[ R ] (Txout R × Sechash R × 𝕂² R)
record ℝ (R : Run) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txout′   : Txout R
    sechash′ : Sechash R
    κ′       : 𝕂² R

𝔾 : Ad → Set
𝔾 ad = Valid ad × Txout (ad .G) × Sechash (ad .G) × 𝕂²′ ad

Txout≈ : _≈_ ⇒² _→⦅ Txout ⦆_
Txout≈ {Γ}{Γ′} = permute-↦ {P = const TxInput′} ∘ ≈⇒namesʳ↭ {Γ}{Γ′}

Sechash≈ : _≈_ ⇒² _→⦅ Sechash ⦆_
Sechash≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒namesˡ↭ {Γ}{Γ′}

𝕂²≈ : _≈_ ⇒² _→⦅ 𝕂² ⦆_
𝕂²≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒ads↭ {Γ}{Γ′}

lift_—⟨_⟩—_⊣_ : ∀ {Z A B : Set} {Z′ : Set} {P : Pred₀ Z′}
  → ⦃ _ : A has Z ⦄ → ⦃ _ : B has Z ⦄
  → (a : A) (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′) (b : B)
  → b ≡⦅ f ⦆ a
    --————————————————————————————————————————————————————
  → a →⦅ (λ x → f x ↦′ P) ⦆ b
(lift _ —⟨ _ ⟩— _ ⊣ eq) m rewrite eq = m

txout∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → Txout Γₜ′
  → Txout R
  → Txout (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
txout∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) txoutˡ txoutʳ
    rewrite namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
          = txoutʳ ++/↦ (Txout≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) txoutˡ)

sechash∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → Sechash Γₜ′
  → Sechash R
  → Sechash (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
sechash∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) sechashˡ sechashʳ
    rewrite namesˡ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
          = sechashʳ ++/↦ (Sechash≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) sechashˡ)

Txout∈ : Txout R → Γ ∈ allCfgs R → Txout Γ
Txout∈ txout Γ∈ = txout ∘ mapMaybe-⊆ isInj₂ (⊆-concatMap⁺ (L.Mem.∈-map⁺ collect Γ∈))

Sechash∈ : Sechash R → Γ ∈ allCfgs R → Sechash Γ
Sechash∈ sechash Γ∈ = sechash ∘ mapMaybe-⊆ isInj₁ (⊆-concatMap⁺ (L.Mem.∈-map⁺ collect Γ∈))

ℝ⊆ : (xy∈ : (Γₜ , Γₜ′) ⋯∈ᵗ R) → ℝ R → ℝ (splitRunˡ R xy∈)
ℝ⊆ {R = R} xy∈ᵗ 𝕣 =
  let
    open ℝ 𝕣
    tr  = R ∙trace′
    R′  = splitRunˡ R xy∈ᵗ
    tr′ = R′ ∙trace′
    tr⊆ = ⊆ˢ-splitTraceˡ tr xy∈ᵗ

    Txout⊆ : R →⦅ Txout ⦆ R′
    Txout⊆ txoutR = txoutR ∘ mapMaybe-⊆ isInj₂ (⊆ˢ⇒names⊆ tr′ tr tr⊆)

    Sechash⊆ : R →⦅ Sechash ⦆ R′
    Sechash⊆ sechashR = sechashR ∘ mapMaybe-⊆ isInj₁ (⊆ˢ⇒names⊆ tr′ tr tr⊆)

    𝕂⊆ : R →⦅ 𝕂² ⦆ R′
    𝕂⊆ κ = κ ∘ (⊆ˢ⇒ads⊆ tr′ tr tr⊆)
  in
    [txout:   Txout⊆ txout′
    ∣sechash: Sechash⊆ sechash′
    ∣κ:       𝕂⊆ κ′
    ]

ℍ[C-Advertise]⇒TxoutG : ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆ → Txout Γ → Txout (ad .G)
ℍ[C-Advertise]⇒TxoutG {Γ = Γ} {ad = ad} (_ , _ , _ , d⊆) txout = weaken-↦ txout (deposits⊆⇒namesʳ⊆ {ad}{Γ} d⊆)

committed⇒ℍ[C-AuthCommit]∗ :
    R ≈⋯ Γ₀ at t
  → nub-participants ad ⊆ committedParticipants ad Γ₀
  → Sechash R
  → (∀ {p} → p ∈ nub-participants ad →
      ∃ λ Γ → ∃ λ Γ′ → ∃ λ secrets →
          ℍ[C-AuthCommit]⦅ Γ ↝ Γ′ ⦆⦅ ad , p , secrets ⦆
        × Sechash Γ′)
committed⇒ℍ[C-AuthCommit]∗ {R}{Γ₀}{t}{ad} R≈ committedA sechash′ {p} p∈ =
  let
    authCommit∈′ : p auth[ ♯▷ ad ] ∈ᶜ Γ₀
    authCommit∈′ = committed⇒authCommit {Γ = Γ₀} $ committedA p∈

    Δ , x , x′ , y , y′ , xy∈ , (_ , y≈) , ℍ = auth-commit∈≈⇒ℍ {R}{Γ₀} R≈ authCommit∈′
    _ , y∈ = ∈-allTransitions⁻ (R .trace .proj₂) xy∈

    sechash-y : Sechash y′
    sechash-y = Sechash≈ {x = y}{y′} y≈
              $ Sechash∈ {R = R} sechash′ y∈
  in
    x′ , y′ , Δ , ℍ , sechash-y

committed⇒ℍ[C-AuthCommit]∗′ :
    (Γ₀ , Γ₀′) ⋯∈ R
  → nub-participants ad ⊆ committedParticipants ad Γ₀
  → Sechash R
  → (∀ {p} → p ∈ nub-participants ad →
      ∃ λ Γ → ∃ λ Γ′ → ∃ λ secrets →
          ℍ[C-AuthCommit]⦅ Γ ↝ Γ′ ⦆⦅ ad , p , secrets ⦆
        × Sechash Γ′)
committed⇒ℍ[C-AuthCommit]∗′ {Γ₀}{_}{R}{ad} xy∈ committedA sechash′ {p} p∈ =
  let
    authCommit∈′ : p auth[ ♯▷ ad ] ∈ᶜ Γ₀
    authCommit∈′ = committed⇒authCommit {Γ = Γ₀} $ committedA p∈

    Δ , x , x′ , y , y′ , xy∈ , (_ , y≈) , ℍ = auth-commit∈≈⇒ℍ′ {Γ₀}{_}{R} xy∈ authCommit∈′
    _ , y∈ = ∈-allTransitions⁻ (R .trace .proj₂) xy∈

    sechash-y : Sechash y′
    sechash-y = Sechash≈ {x = y}{y′} y≈
              $ Sechash∈ {R = R} sechash′ y∈
  in
    x′ , y′ , Δ , ℍ , sechash-y

ℍ[C-AuthCommit]∗⇒SechashG :
    (∀ {p} → p ∈ nub-participants ad →
      ∃ λ Γ → ∃ λ Γ′ → ∃ λ secrets →
          ℍ[C-AuthCommit]⦅ Γ ↝ Γ′ ⦆⦅ ad , p , secrets ⦆
        × Sechash Γ′)
  → Sechash (ad .G)
ℍ[C-AuthCommit]∗⇒SechashG {ad} ∀p {s} s∈ =
  let
    partG = nub-participants ad; ⟨ G ⟩ _ = ad
    pₛ , pₛ∈ = namesˡ⇒part {g = G} s∈
    _ , Γₛ ,  secrets , (Γ₁ , _ , Γₛ≡ , as≡ , _) , SechashΓₛ = ∀p pₛ∈
    -- Γₛ≡ : Γₛ ≡ ` ad ∣ Γ₁ ∣ Δ ∣ pₛ auth[ ♯▷ ad ]
    (as , ms) = unzip secrets; Δ = || map (uncurry ⟨ pₛ ∶_♯_⟩) secrets
    -- as≡ : as ≡ secretsOfᵖ pₛ G

    s∈Δ : s ∈ namesˡ Δ
    s∈Δ = namesʳ-∥map-authCommit {A = pₛ} {secrets = secrets} (⟪ s L.Mem.∈_ ⟫ as≡ ~: names⊆secretsOf {g = G} s∈)

    n⊆ : namesˡ Δ ⊆ namesˡ (` ad ∣ Γ₁ ∣ Δ ∣ pₛ auth[ ♯▷ ad ])
    n⊆ = mapMaybe-⊆ isInj₁
       $ ∈-collect-++⁺ˡ (` ad ∣ Γ₁ ∣ Δ) (pₛ auth[ ♯▷ ad ])
       ∘ ∈-collect-++⁺ʳ (` ad ∣ Γ₁) Δ

    s∈′ : s ∈ namesˡ Γₛ
    s∈′ = ⟪ (λ ◆ → s ∈ namesˡ ◆) ⟫ Γₛ≡ ~: n⊆ s∈Δ
  in
    SechashΓₛ {s} s∈′
