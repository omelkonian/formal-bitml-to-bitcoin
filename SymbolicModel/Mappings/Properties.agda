open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Membership
open import Prelude.Collections
open import Prelude.Setoid
open import Prelude.Traces
open import Prelude.General

open import Bitcoin using (TxInput′)

module SymbolicModel.Mappings.Properties
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
  hiding (_∎; begin_)
open import SymbolicModel.Accessors Participant Honest
open import SymbolicModel.Collections Participant Honest
open import SymbolicModel.Mappings.Base Participant Honest

Txout≈ : _≈_ ⇒² _→⦅ Txout ⦆_
Txout≈ {Γ}{Γ′} = permute-↦ {P = const TxInput′} ∘ ≈⇒namesʳ↭ {Γ}{Γ′}

Txout≗ : ∀ (Γ≈ : Γ ≈ Γ′) (txoutΓ : Txout Γ) →
  Txout≈ {Γ}{Γ′} Γ≈ txoutΓ ≗⟨ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈ ⟩↦ txoutΓ
Txout≗ {Γ}{Γ′} Γ≈ txoutΓ = permute-≗↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txoutΓ

Sechash≈ : _≈_ ⇒² _→⦅ Sechash ⦆_
Sechash≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒namesˡ↭ {Γ}{Γ′}

Sechash≗ : ∀ (Γ≈ : Γ ≈ Γ′) (sechashΓ : Sechash Γ) →
  Sechash≈ {Γ}{Γ′} Γ≈ sechashΓ ≗⟨ ≈⇒namesˡ↭ {Γ}{Γ′} Γ≈ ⟩↦ sechashΓ
Sechash≗ {Γ}{Γ′} Γ≈ sechashΓ = permute-≗↦ (≈⇒namesˡ↭ {Γ}{Γ′} Γ≈) sechashΓ

𝕂²≈ : _≈_ ⇒² _→⦅ 𝕂² ⦆_
𝕂²≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒ads↭ {Γ}{Γ′}

𝕂²≗ : ∀ (Γ≈ : Γ ≈ Γ′) (κΓ : 𝕂² Γ) →
  𝕂²≈ {Γ}{Γ′} Γ≈ κΓ ≗⟨ ≈⇒ads↭ {Γ}{Γ′} Γ≈ ⟩↦ κΓ
𝕂²≗ {Γ}{Γ′} Γ≈ κΓ = permute-≗↦ (≈⇒ads↭ {Γ}{Γ′} Γ≈) κΓ

lift_—⟨_⟩—_⊣_ : ∀ {Z A B : Set} {Z′ : Set} {P : Pred₀ Z′}
  → ⦃ _ : A has Z ⦄ → ⦃ _ : B has Z ⦄
  → (a : A) (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′) (b : B)
  → b ≡⦅ f ⦆ a
    --————————————————————————————————————————————————————
  → a →⦅ (λ x → f x ↦′ P) ⦆ b
(lift _ —⟨ _ ⟩— _ ⊣ eq) fa = ⟪ _↦′ _ ⟫ eq ~: fa

lift≗_—⟨_⟩—_⊣_ : ∀ {Z A B : Set} {Z′ : Set} {P : Pred₀ Z′} ⦃ _ : A has Z ⦄ → ⦃ _ : B has Z ⦄
  → (a : A) (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′) (b : B)
  → (eq : b ≡⦅ f ⦆ a)
  → (mapA : f a ↦′ P)
  → (lift a —⟨ f ⟩— b ⊣ eq) mapA ≗⟨ ↭-reflexive $ sym $ eq ⟩↦ mapA
(lift≗ _ —⟨ _ ⟩— _ ⊣ eq) _ _ rewrite eq = refl

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

ℝ-base : ∀ {init : Initial Γₜ}
  → ℾᵗ Γₜ
  → ℝ (Γₜ ∎⊣ init)
ℝ-base {init = i} ℽ =
  [txout:   substʳ (_↦ TxInput′) (namesʳ-∎ {init = i}) txoutΓ
  ∣sechash: substʳ (_↦ ℤ)        (namesˡ-∎ {init = i}) sechashΓ
  ∣κ:       substʳ (_↦′ 𝕂²′)     (ads-∎    {init = i}) κΓ
  ] where open ℾᵗ ℽ

𝕃 : Run → Cfgᵗ → Set
𝕃 R Γₜ = Σ[ 𝕒 ∈ 𝔸 R Γₜ ] ℾᵗ (𝕒 .proj₂ .proj₂ .proj₁)

ℝ-step : ℝ R → (λˢ : 𝕃 R Γₜ) → ℝ (Γₜ ∷ R ⊣ λˢ .proj₁)
ℝ-step {R = R} 𝕣 ((_ , _ , _ , Γ→ , eq) , ℽ) =
  [txout:   txout∷   {R = R} Γ→ eq txoutΓ    txout′
  ∣sechash: sechash∷ {R = R} Γ→ eq sechashΓ  sechash′
  ∣κ:       κ∷       {R = R} Γ→ eq κΓ        κ′
  ] where open ℝ 𝕣; open ℾᵗ ℽ

txout∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ Txout ⦆ Rˢ
txout∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) txout′ =
  destruct≡-++/↦ {zs = namesʳ (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (namesʳ-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    txout′ .proj₁

sechash∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ Sechash ⦆ Rˢ
sechash∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) sechash′ =
  destruct≡-++/↦ {zs = namesˡ (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (namesˡ-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    sechash′ .proj₁

κ∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ 𝕂² ⦆ Rˢ
κ∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) κ′ =
  destruct≡-++/↦ {zs = advertisements (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (ads-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    κ′ .proj₁

drop-ℝ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) → ℝ (Γₜ ∷ Rˢ ⊣ 𝕒) → ℝ Rˢ
drop-ℝ {Rˢ = Rˢ} 𝕒 𝕣′ =
  [txout:   txout∷˘   {Rˢ = Rˢ} 𝕒 txout′
  ∣sechash: sechash∷˘ {Rˢ = Rˢ} 𝕒 sechash′
  ∣κ:       κ∷˘       {Rˢ = Rˢ} 𝕒 κ′
  ] where open ℝ 𝕣′

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

Suffix⊆-subst : ∀ {X : Set ℓ} {xs ys zs : List X} (eq : ys ≡ zs) (xs⊆ : xs ⊆ ys)
  → Suffix⊆ xs⊆
  → Suffix⊆ (subst (_ L.Mem.∈_) eq ∘ xs⊆)
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
          (sym $ ↭-sym∘≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) ⟩
    ( permute-↦ (↭-sym $ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈)
    $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout
    ) x∈
  ≡⟨ permute-↦∘permute-↦˘ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout x∈ ⟩
    txout x∈
  ∎ where open ≡-Reasoning

-- Txout≈∘lift∘Txout≈⁻¹ : ∀ {Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′) (txout : Txout Γ)
--   (namesʳ≡ : Γ′ ≡⦅ namesʳ ⦆ Γ″)
--   → ( Txout≈ {Γ″}{Γ} (↭-sym Γ≈)
--     $ (lift Γ′ —⟨ namesʳ ⟩— Γ″ ⊣ namesʳ≡)
--     $ Txout≈ {Γ}{Γ′} Γ≈ txout
--     )
--   ≗↦ txout
-- Txout≈∘lift∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txout {x} x∈ =

++/↦-Txout≈∘Txout≈⁻¹ : ∀ {Γ₀ Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′)
  (txoutˡ : Txout Γ₀)
  (txoutʳ : Txout Γ)
  →  (txoutˡ ++/↦ (Txout≈ {Γ′}{Γ} (↭-sym Γ≈) $ Txout≈ {Γ}{Γ′} Γ≈ txoutʳ))
  ≗↦ (txoutˡ ++/↦ txoutʳ)
++/↦-Txout≈∘Txout≈⁻¹ {Γ₀}{Γ}{Γ′} Γ≈ txoutˡ txoutʳ {x} x∈
  with L.Mem.∈-++⁻ (namesʳ Γ₀) x∈
... | inj₁ _  = refl
... | inj₂ y∈ = Txout≈∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txoutʳ y∈
