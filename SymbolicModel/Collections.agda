{-# OPTIONS --allow-unsolved-metas #-}
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
open import Prelude.Accessors
open import Prelude.InferenceRules


open import Bitcoin.Crypto
open import Bitcoin.Tx

module SymbolicModel.Collections
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
  hiding ( _∎; begin_)

open ≡-Reasoning

private variable X : Set

instance
  HXʳ : ⦃ ∀ {Γₜ Γₜ′} → (Γₜ —↠ₜ Γₜ′) has X ⦄ → Run has X
  HXʳ ⦃ h ⦄ .collect = collect ⦃ h ⦄ ∘ trace

-- [BUG] instantiated `advertisements ⦃ HAʳ ⦄`, to aid Agda's type inference
authorizedHonAdsʳ : Run → List Advertisement
authorizedHonAdsʳ = collect

unquoteDecl _∙Cfg _∙cfg ∙cfg=_ = genAccessor _∙Cfg _∙cfg ∙cfg=_ (quote Cfg)
instance
  Cfgᵗ∙Cfg : Cfgᵗ ∙Cfg
  Cfgᵗ∙Cfg = ∙cfg= cfg

  Run∙Cfg : Run ∙Cfg
  Run∙Cfg = ∙cfg= (_∙cfg ∘ end)

ads⦅end⦆⊆ : ∀ R → advertisements (R .end) ⊆ advertisements R
ads⦅end⦆⊆ R
  = ⊆-concat⁺
  $ L.Mem.∈-map⁺ advertisements
  $ L.Mem.∈-map⁺ cfg
  $ end∈allCfgsᵗ R

names⦅end⦆⊆ : (R : Run) → names (R .end) ⊆ names R
names⦅end⦆⊆ R = ⊆-concat⁺
              $ L.Mem.∈-map⁺ names
              $ L.Mem.∈-map⁺ cfg
              $ end∈allCfgsᵗ R

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

names-∎ : ∀ {init : Initial Γₜ₀}
  → names (Γₜ₀ ∎⊣ init)
  ≡ names Γₜ₀
names-∎ = L.++-identityʳ _

namesˡ-∎ : ∀ {init : Initial Γₜ₀}
  → namesˡ (Γₜ₀ ∎⊣ init)
  ≡ namesˡ Γₜ₀
namesˡ-∎ {Γ₀}{init} = cong filter₁ $ names-∎ {Γ₀}{init}

namesʳ-∎ : ∀ {init : Initial Γₜ₀}
  → namesʳ (Γₜ₀ ∎⊣ init)
  ≡ namesʳ Γₜ₀
namesʳ-∎ {Γ₀}{init} = cong filter₂ $ names-∎ {Γ₀}{init}

ads-∎ : ∀ {init : Initial Γₜ₀}
  → advertisements (Γₜ₀ ∎⊣ init)
  ≡ advertisements Γₜ₀
ads-∎ = L.++-identityʳ _

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
-- (issue appears at the usage site)
-- ℝ = ∃[ R ] (Txout R × Sechash R × 𝕂² R)
record ℝ (R : Run) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txout′   : Txout   R
    sechash′ : Sechash R
    κ′       : 𝕂²      R

-- [BUG] this also create issues (unresolved instances nonsense)
-- record 𝕏 ⦃ _ : X has Name ⦄ ⦃ _ : X has Advertisement ⦄ (x : X) : Set where
--   constructor [txout:_∣sechash:_∣κ:_]
--   field
--     txout′   : Txout   x
--     sechash′ : Sechash x
--     κ′       : 𝕂²      x

-- ℾᵗ : Pred₀ Cfgᵗ
-- ℾᵗ = 𝕏 {X = Cfgᵗ} ⦃ it ⦄ ⦃ it ⦄

record ℾᵗ (Γₜ : Cfgᵗ) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txoutΓ   : Txout   Γₜ
    sechashΓ : Sechash Γₜ
    κΓ       : 𝕂²      Γₜ

-- ℾ : Pred₀ Cfg
-- ℾ = 𝕏 {X = Cfg} ⦃ it ⦄ ⦃ it ⦄

record ℾ (Γ : Cfg) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txoutΓ   : Txout   Γ
    sechashΓ : Sechash Γ
    κΓ       : 𝕂²      Γ

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

Txout∈ : Txout R → Γ ∈ allCfgs R → Txout Γ
Txout∈ txout Γ∈ = txout ∘ mapMaybe-⊆ isInj₂ (⊆-concat⁺ (L.Mem.∈-map⁺ collect Γ∈))

Sechash∈ : Sechash R → Γ ∈ allCfgs R → Sechash Γ
Sechash∈ sechash Γ∈ = sechash ∘ mapMaybe-⊆ isInj₁ (⊆-concat⁺ (L.Mem.∈-map⁺ collect Γ∈))

txout∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → Txout Γₜ′
  → Txout R
  → Txout (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
txout∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) txoutΓ′ txoutR
  = subst (_↦ TxInput′) (sym $ namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
  $ txoutR ++/↦ Txout≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) txoutΓ′

sechash∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → Sechash Γₜ′
  → Sechash R
  → Sechash (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
sechash∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) sechashˡ sechashʳ
    rewrite namesˡ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
          = sechashʳ ++/↦ (Sechash≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) sechashˡ)

κ∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → 𝕂² Γₜ′
  → 𝕂² R
  → 𝕂² (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
κ∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) κˡ κʳ
    rewrite ads-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
          = κʳ ++/↦ (𝕂²≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) κˡ)

ℝ-base : {init : Initial Γₜ}
  → ℾᵗ Γₜ
  → ℝ (Γₜ ∎⊣ init)
ℝ-base {init = i} ℽ =
  [txout:   substʳ (_↦ TxInput′) (namesʳ-∎ {init = i}) txoutΓ
  ∣sechash: substʳ (_↦ ℤ)        (namesˡ-∎ {init = i}) sechashΓ
  ∣κ:       substʳ (_↦′ 𝕂²′)     (ads-∎    {init = i}) κΓ
  ] where open ℾᵗ ℽ

ℝ-step : ℝ R → (𝕒 : 𝔸 R Γₜ) → ℾᵗ (𝕒 .proj₂ .proj₂ .proj₁) → ℝ (Γₜ ∷ R ⊣ 𝕒)
ℝ-step {R = R} 𝕣 (_ , _ , _ , Γ→ , eq) ℽ =
  [txout:   txout∷   {R = R} Γ→ eq txoutΓ    txout′
  ∣sechash: sechash∷ {R = R} Γ→ eq sechashΓ  sechash′
  ∣κ:       κ∷       {R = R} Γ→ eq κΓ        κ′
  ] where open ℝ 𝕣; open ℾᵗ ℽ

𝔸ℾ : Run → Cfgᵗ → Set
𝔸ℾ R Γₜ =
  Σ[ 𝕒 ∈ 𝔸 R Γₜ ]
    ℾᵗ (𝕒 .proj₂ .proj₂ .proj₁)

data ℝ∗ : Run → Set where
  _∎⊣_✓ :
      ℾᵗ Γₜ
    → (init : Initial Γₜ)
      --—————————————
    → ℝ∗ (Γₜ ∎⊣ init)

  _∷_⊣_✓ :
    ∀ Γₜ
    → ℝ∗ R
    → (𝕒ℽ : 𝔸ℾ R Γₜ)
      --—————————————————————————
    → ℝ∗ (Γₜ ∷ R ⊣ 𝕒ℽ .proj₁)

ℝ∗⇒ℝ : ℝ∗ ⊆¹ ℝ
ℝ∗⇒ℝ {R} = λ where
  (ℽ ∎⊣ init ✓)       → ℝ-base {init = init} ℽ
  (_ ∷ 𝕣 ⊣ (𝕒 , ℽ) ✓) → ℝ-step (ℝ∗⇒ℝ 𝕣) 𝕒 ℽ

Last∈-end∈allCfgsᵗ : ∀ R → Last∈ (end∈allCfgsᵗ R)
Last∈-end∈allCfgsᵗ R = go (R ∙trace′)
  where
    go : ∀ (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Last∈ (⟫end∈allCfgsᵗ.go tr)
    go = λ where
      (_ ∎ₜ)               → refl
      (_ —→ₜ⟨ _ ⟩ _ ⊢ tr′) → go tr′

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

Suffix⊆-subst : ∀ {xs ys zs : List X} (eq : ys ≡ zs) (xs⊆ : xs ⊆ ys) →
  Suffix⊆ xs⊆
  ────────────────────────────────────
  Suffix⊆ (subst (_ L.Mem.∈_) eq ∘ xs⊆)
Suffix⊆-subst refl _ p = p

txout∷∘namesʳ⦅end⦆⊆ : (Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → let R′ = Γₜ″ ⟨ Γ→Γ′ ⟩←—— R ⊣ eq in
  (txoutΓ′ : Txout Γₜ′)
  (txoutR : Txout R)
  → ∀ {x : Id} (x∈ : x ∈ namesʳ Γₜ″)
  --————————————————————————
  → (txout∷ {R = R} Γ→Γ′ eq txoutΓ′ txoutR) (namesʳ⦅end⦆⊆ R′ x∈)
  ≡ Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ eq .proj₁ .proj₂) txoutΓ′ x∈
txout∷∘namesʳ⦅end⦆⊆ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→Γ′ eq@((_ , Γ≈) , _) txoutΓ′ txoutR {x} x∈
  = ++/↦≡-inj₂ n≡ _ _ _ _ is-inj₂
  where
    _R′ = Γₜ″ ⟨ Γ→Γ′ ⟩←—— R ⊣ eq

    n≡ : namesʳ _R′ ≡ namesʳ R ++ namesʳ Γₜ″
    n≡ = namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→Γ′ eq

    x∈₁ : x ∈ namesʳ _R′
    x∈₁ = namesʳ⦅end⦆⊆ _R′ x∈

    x∈₂ : x ∈ namesʳ R ++ namesʳ Γₜ″
    x∈₂ = subst (x L.Mem.∈_) n≡ x∈₁

    n⊆₀ : names Γₜ″ ⊆ names _R′
    n⊆₀ = ⊆-concat⁺ $ L.Mem.∈-map⁺ names $ L.Mem.∈-map⁺ cfg $ end∈allCfgsᵗ _R′

    n⊆₁ : namesʳ Γₜ″ ⊆ namesʳ _R′
    n⊆₁ = mapMaybe-⊆ isInj₂ n⊆₀

    n⊆ : namesʳ Γₜ″ ⊆ namesʳ R ++ namesʳ Γₜ″
    n⊆ = subst (_ L.Mem.∈_) n≡ ∘ n⊆₁

    suffix-n⊆ : Suffix⊆ n⊆
    suffix-n⊆ = Suffix⊆-subst n≡ n⊆₁
              $ Suffix⊆-mapMaybe isInj₂ n⊆₀
              $ Last∈-concat (L.Mem.∈-map⁺ names $ L.Mem.∈-map⁺ cfg $ end∈allCfgsᵗ _R′)
              $ Last∈-map⁺ names (L.Mem.∈-map⁺ cfg $ end∈allCfgsᵗ _R′)
              $ Last∈-map⁺ cfg (end∈allCfgsᵗ _R′)
              $ Last∈-end∈allCfgsᵗ _R′

    is-inj₂ : L.Mem.∈-++⁻ (namesʳ R) {namesʳ Γₜ″} x∈₂ ≡ inj₂ x∈
    is-inj₂ = Suffix⊆-++⁻ _ _ suffix-n⊆

Txout≈∘Txout≈⁻¹ : ∀ {Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′) (txout : Txout Γ)
  → Txout≈ {Γ′}{Γ} (↭-sym Γ≈) (Txout≈ {Γ}{Γ′} Γ≈ txout) ≗↦ txout
Txout≈∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txout {x} x∈ =
  begin
    ( Txout≈ {Γ′}{Γ} (↭-sym Γ≈)
    $ Txout≈ {Γ}{Γ′} Γ≈ txout
    ) x∈
  ≡⟨⟩
    ( permute-↦ (≈⇒namesʳ↭ {Γ′}{Γ} $ ↭-sym Γ≈)
    $ Txout≈ {Γ}{Γ′} Γ≈ txout
    ) x∈
  ≡⟨⟩
    ( permute-↦ (≈⇒namesʳ↭ {Γ′}{Γ} $ ↭-sym Γ≈)
    $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout
    ) x∈
  ≡⟨ cong (λ ◆ → (permute-↦ ◆ $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout) x∈)
          (≈⇒namesʳ↭∘↭-sym {Γ}{Γ′} Γ≈) ⟩
    ( permute-↦ (↭-sym $ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈)
    $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout
    ) x∈
  ≡⟨ permute-↦∘permute-↦˘ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout x∈ ⟩
    txout x∈
  ∎

++/↦-Txout≈∘Txout≈⁻¹ : ∀ {Γ₀ Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′)
  (txoutˡ : Txout Γ₀)
  (txoutʳ : Txout Γ)
  →  (txoutˡ ++/↦ (Txout≈ {Γ′}{Γ} (↭-sym Γ≈) $ Txout≈ {Γ}{Γ′} Γ≈ txoutʳ))
  ≗↦ (txoutˡ ++/↦ txoutʳ)
++/↦-Txout≈∘Txout≈⁻¹ {Γ₀}{Γ}{Γ′} Γ≈ txoutˡ txoutʳ {x} x∈
  with L.Mem.∈-++⁻ (namesʳ Γ₀) x∈
... | inj₁ _  = refl
... | inj₂ y∈ = Txout≈∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txoutʳ y∈

open L.Perm using (∈-resp-↭)

txout∷∘Txout≈₁ : ∀ {R} {α} {Γ}{t}{t′}{Γₜ″ : Cfgᵗ} {ad} →
    let Γₜ = Γ at t; Γₜ′ = (` ad ∣ Γ) at t′ in
    (x∈ : x ∈ namesʳ (R .end))
  → (txout : Txout R)
  → (Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → let R′ = Γₜ″ ⟨ Γ→Γ′ ⟩←—— R ⊣ eq in
    (namesʳ↭ : R .end ↭⦅ namesʳ ⦆ R′ .end)
    --——————————————————–––––––––——–
  → txout∷ {R = R} Γ→Γ′ eq
           (Txout≈ {R ∙cfg}{Γ} (eq .proj₂ .proj₂) (txout ∘ namesʳ⦅end⦆⊆ R))
           txout
           (namesʳ⦅end⦆⊆ R′ $ ∈-resp-↭ namesʳ↭ x∈)
  ≡ txout (namesʳ⦅end⦆⊆ R x∈)
txout∷∘Txout≈₁ {x = x}{R = R}{α}{Γ}{t}{t′}{Γₜ″@(Γ″ at _)}{ad}
  x∈ txout Γ→ eq@((_ , Γ≈) , (_ , ≈Γ)) names↭ =
  -- txout∷∘namesʳ⦅end⦆⊆ Γ→Γ eq (Txout≈ {R ∙cfg}{Γ} (eq .proj₂ .proj₂) (txout ∘ namesʳ⦅end⦆⊆ R)) txout x∈
  let
    Γ′  = ` ad ∣ Γ
    _R′ = Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq
  in begin
    txout∷ {R = R} Γ→ eq
           (Txout≈ {R ∙cfg}{Γ} ≈Γ (txout ∘ namesʳ⦅end⦆⊆ R))
           txout
           (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
  -- ≡⟨ txout∷∘namesʳ⦅end⦆⊆ -- {Γₜ}{α}{Γₜ′}{R .end}{R}
  --      Γ→ ?
  --      ((Txout≈ {R ∙cfg}{Γ} ≈Γ (txout ∘ namesʳ⦅end⦆⊆ R)))
  --      txout
  --      (∈-resp-↭ names↭ x∈) ⟩
  ≡⟨ {!!} ⟩
    Txout≈ {Γ′}{Γ″} (↭-sym Γ≈)
      (Txout≈ {R ∙cfg}{Γ} ≈Γ (txout ∘ namesʳ⦅end⦆⊆ R))
      (∈-resp-↭ names↭ x∈)
  -- ≡⟨ Txout≈∘Txout≈⁻¹ {Γₜ″ .cfg} {Γₜ′ .cfg}
  --      (eq . proj₁ .proj₂) (txout ∘ namesʳ⦅end⦆⊆ R) (∈-resp-↭ names↭ x∈) ⟩
  --   ( txout
  --   ∘ namesʳ⦅end⦆⊆ R
  --   ∘ ∈-resp-↭ names↭
  --   ) x∈
  ≡⟨ {!!} ⟩
    ( txout
    ∘ namesʳ⦅end⦆⊆ R
    ) x∈
  ∎

txout∷∘Txout≈ : ∀ {α} {Γₜ Γₜ′ Γₜ″ : Cfgᵗ}
  → (x∈ : x ∈ namesʳ (R .end))
  → (txout : Txout R)
  → (Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → let R′ = Γₜ″ ⟨ Γ→Γ′ ⟩←—— R ⊣ eq in
    (txout′ : Txout R′)
    (names↭ : R .end ↭⦅ namesʳ ⦆ R′ .end)
    --——————————————————–––––––––——–
  → txout∷ {R = R} Γ→Γ′ eq
           (Txout≈ {Γₜ″ ∙cfg}{Γₜ′ ∙cfg} (eq .proj₁ .proj₂) (txout′ ∘ namesʳ⦅end⦆⊆ R′))
           txout
           (namesʳ⦅end⦆⊆ R′ $ ∈-resp-↭ names↭ x∈)
  ≡ txout (namesʳ⦅end⦆⊆ R x∈)
txout∷∘Txout≈ {x = x} {R = R} {α = α}{Γₜ@(Γ at _)}{Γₜ′@(Γ′ at _)}{Γₜ″@(Γ″ at _)}
              x∈ txout Γ→ eq@((_ , Γ≈), _) txout′ names↭
  -- rewrite namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
  -- rewrite Txout≈∘Txout≈⁻¹ {Γ}{Γ′} Γ≈
  --                         (txout′ ∘ namesʳ⦅end⦆⊆ (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq))
  --                         (namesʳ⦅end⦆⊆ R x∈)
  -- = {!x∈!}
  = begin
    txout∷ {R = R} Γ→ eq
           (Txout≈ {Γ″}{Γ′} Γ≈ (txout′ ∘ namesʳ⦅end⦆⊆ _R′))
           txout
           (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
  ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {Γₜ}{α}{Γₜ′}{Γₜ″}{R} Γ→ eq
       ((Txout≈ {Γ″}{Γ′} Γ≈ (txout′ ∘ namesʳ⦅end⦆⊆ _R′)))
       txout
       (∈-resp-↭ names↭ x∈) ⟩
    Txout≈ {Γ′} {Γ″} (↭-sym Γ≈)
      (Txout≈ {Γₜ″ ∙cfg}{Γₜ′ ∙cfg} Γ≈ (txout′ ∘ namesʳ⦅end⦆⊆ _R′))
      (∈-resp-↭ names↭ x∈)
  ≡⟨ Txout≈∘Txout≈⁻¹ {Γ″} {Γ′} Γ≈ (txout′ ∘ namesʳ⦅end⦆⊆ _R′) (∈-resp-↭ names↭ x∈) ⟩
    ( txout′
    ∘ namesʳ⦅end⦆⊆ _R′
    ∘ ∈-resp-↭ names↭
    ) x∈
  -- ≡⟨⟩
  --   ( subst (_↦ TxInput′) (sym $ namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
  --   $ (txout ++/↦ ( Txout≈ {Γ′}{Γ″} (↭-sym Γ≈)
  --                 $ Txout≈ {Γ″}{Γ′} Γ≈
  --                 $ txout′ ∘ namesʳ⦅end⦆⊆ _R′)))
  --   (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
  ≡⟨ {!!} ⟩
  --   (txout ++/↦ ( Txout≈ {Γ′}{Γ″} (↭-sym Γ≈)
  --               $ Txout≈ {Γ″}{Γ′} Γ≈
  --               $ txout′ ∘ namesʳ⦅end⦆⊆ _R′))
  --   ( subst (x L.Mem.∈_) (namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
  --   $ (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
  --   )
  -- ≡⟨ ++/↦-Txout≈∘Txout≈⁻¹ {Γ₀ = {!!}} Γ≈ txout (txout′ ∘ namesʳ⦅end⦆⊆ _R′)
  --      $ ( subst (x L.Mem.∈_) (namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
  --        $ (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
  --        ) ⟩
    (txout ++/↦ (txout′ ∘ namesʳ⦅end⦆⊆ _R′))
    ( subst (x L.Mem.∈_) (namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
    $ (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
    )
  ≡⟨ {!!} ⟩
    ( txout
    ∘ namesʳ⦅end⦆⊆ R
    ) x∈
  ∎
  where
    _R′ = Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq

    HELL : L.Mem.∈-++⁻ (namesʳ R) {namesʳ Γ″}
             ( subst (x L.Mem.∈_) (namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
             $ (namesʳ⦅end⦆⊆ _R′ $ ∈-resp-↭ names↭ x∈)
             )
           ≡ inj₁ (namesʳ⦅end⦆⊆ R x∈)
    HELL = {!!}
