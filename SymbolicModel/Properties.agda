open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Traces
open import Prelude.InferenceRules
open import Prelude.Lists.Mappings
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.Concat
open import Prelude.Lists.Membership
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Setoid

open import Bitcoin using (TxInput′)
open import BitML.BasicTypes using (⋯)

module SymbolicModel.Properties (⋯ : ⋯) (let open ⋯ ⋯) where

open import Compiler.Mappings ⋯
open import SymbolicModel.Run ⋯
open import SymbolicModel.Mappings ⋯

∃[_∋ʳ_] : Run → Rel₀ Cfg → Type
∃[ R ∋ʳ P ] = ∃[ R ∙trace′ ∋ P ]

ad∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ ` ad ∈ᶜ Γ
    ───────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-Advertise]⦅_↝_⦆⦅ ad ⦆ ]
ad∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) ad∈ =
  traceAd∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) ad∈) tr

auth-commit∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ A auth[ ♯▷ ad ] ∈ᶜ Γ
    ────────────────────────────────────────────────────
    ∃ λ Δ → ∃[ R ∋ʳ ℍ[C-AuthCommit]⦅_↝_⦆⦅ ad , A , Δ ⦆ ]
auth-commit∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  traceAuthCommit∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

auth-init∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ A auth[ z ▷ˢ ad ] ∈ᶜ Γ
    ──────────────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-AuthInit]⦅_↝_⦆⦅ A , ad , z ⦆ ]
auth-init∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  traceAuthInit∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

auth-control∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ A auth[ z ▷ d ] ∈ᶜ Γ
    ────────────────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-AuthControl]⦅_↝_⦆⦅ A , z , d ⦆ ]
auth-control∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  traceAuthControl∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

c∈≈⇒Ancestor :
  ∙ R ≈⋯ Γ at t
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
    ─────────────────────────────────────
    ∃ λ ad → ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
c∈≈⇒Ancestor {R@record {init = i , _; trace = _ , tr}}{Γ}{t}{c} (_ , Γ≈) c∈ =
  traceContract∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) c∈) tr

ANCESTOR : ∀ {c Γ} →
  ∙ R ≈⋯ Γ at t
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
    ─────────────────────
    ∃ λ ad
    → Valid ad
    × ad ∈ advertisements R
    × c ⊆ subterms ad
    × ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
ANCESTOR {R = R@(record {trace = _ , tr})} {Γ = Γ} R≈ c∈ =
  let ad , ∃H@(_ , _ , _ , _ , _ , _ , _ , ad↝c) = c∈≈⇒Ancestor {R}{Γ} R≈ c∈
      _ , vad , ad∈ = ℍ[C-Init]⇒∃ℍ[C-AuthInit] (R .init) tr (∃-weakenP tr proj₁ ∃H)
  in  ad , vad , ad∈ , h-sub∙↝∗ {ad} ad↝c , ∃H

ℍ[C-Advertise]⇒Txout :
  ∙ ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆
  ∙ Txout Γ
    ──────────────────────────────
    Txout ad × Txout (ad .C)
ℍ[C-Advertise]⇒Txout {Γ = Γ} {ad = ad} (_ , vad , _ , d⊆) txout =
  let txoutG = weaken-↦ txout (deposits⊆⇒namesʳ⊆ {ad}{Γ} d⊆)
  in txoutG , weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)

ℍ[C-Advertise]⇒TxoutG :
  ∙ ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆
  ∙ Txout Γ
    ──────────────────────────────
    Txout ad
ℍ[C-Advertise]⇒TxoutG {Γ = Γ} {ad = ad} ℍ txout =
  ℍ[C-Advertise]⇒Txout {Γ = Γ} {ad = ad} ℍ txout .proj₁

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
    s∈Δ = namesʳ-∥map-authCommit {A = pₛ} {secrets = secrets}
            (⟪ s L.Mem.∈_ ⟫ as≡ ~: names⊆secretsOf {g = G} s∈)

    n⊆ : namesˡ Δ ⊆ namesˡ (` ad ∣ Γ₁ ∣ Δ ∣ pₛ auth[ ♯▷ ad ])
    n⊆ = mapMaybe-⊆ isInj₁
       $ ∈-collect-++⁺ˡ (` ad ∣ Γ₁ ∣ Δ) (pₛ auth[ ♯▷ ad ])
       ∘ ∈-collect-++⁺ʳ (` ad ∣ Γ₁) Δ

    s∈′ : s ∈ namesˡ Γₛ
    s∈′ = ⟪ (λ ◆ → s ∈ namesˡ ◆) ⟫ Γₛ≡ ~: n⊆ s∈Δ
  in
    SechashΓₛ {s} s∈′

ad∈⇒Txout :
  ∙ ` ad ∈ᶜ Γ
  ∙ R ≈⋯ Γ at t
  ∙ Txout R
    ────────────────────────
    Txout ad × Txout (ad .C)
ad∈⇒Txout {ad}{Γ}{R@(record {trace = _ , tr})} ad∈ R≈ txout =
  let
    Γᵢ′ , Γᵢ , _ , _ , xy∈ , (x≈ , _) , ℍ = ad∈≈⇒ℍ {R}{Γ} R≈ ad∈
    Γᵢ∈ , _ = ∈-allTransitions⁻ tr xy∈
    txoutΓᵢ = Txout≈ {Γᵢ′}{Γᵢ} x≈
            $ Txout∈ {R = R} txout Γᵢ∈
  in
    ℍ[C-Advertise]⇒Txout {Γ = Γᵢ}{ad = ad} ℍ txoutΓᵢ

ad∈⇒TxoutG :
  ∙ ` ad ∈ᶜ Γ
  ∙ R ≈⋯ Γ at t
  ∙ Txout R
    ───────────
    Txout ad
ad∈⇒TxoutG {ad}{Γ}{R} ad∈ R≈ txout = ad∈⇒Txout {ad}{Γ}{R} ad∈ R≈ txout .proj₁

auth-commit∈⇒Txout : ∀ {Δ : List (Secret × Maybe ℕ)} →
  ∙ auth-commit⦅ A , ad , Δ ⦆ ∈ labels R
  ∙ ℝ R
    ──────────────────────────────────────
    Txout ad × Txout (ad .C)
auth-commit∈⇒Txout {A}{ad} {R@(record {trace = _ , tr})} α∈ 𝕣 =
  let
    Γᵢ′ , Γᵢ , _ , _ , xy∈ , (x≈ , _) , _ , Γᵢ≡ , _ = auth-commit⇒∗ tr α∈
    Γᵢ∈ , _ = ∈-allTransitions⁻ tr xy∈
    ad∈ : ` ad ∈ᶜ Γᵢ
    ad∈ = subst (` ad ∈ᶜ_) (sym Γᵢ≡) (here refl)

    ad∈′ : ` ad ∈ᶜ Γᵢ′
    ad∈′ = ∈ᶜ-resp-≈ {Γᵢ}{Γᵢ′} (↭-sym x≈) ad∈

    tᵢ , _ , xy∈ᵗ = ×∈⇒×∈ᵗ tr xy∈
    tr′      = splitTraceˡ tr xy∈ᵗ
    R′       = splitRunˡ R xy∈ᵗ

    𝕣′ : ℝ R′
    𝕣′ = ℝ⊆ xy∈ᵗ 𝕣

    R≈′ : R′ ≈⋯ Γᵢ′ at tᵢ
    R≈′ = splitRunˡ-≈⋯ R xy∈ᵗ

    Γⱼ′ , Γⱼ , _ , _ , xy∈′ , (x≈′ , _) , ℍ = ad∈≈⇒ℍ {R′}{Γᵢ′} R≈′ ad∈′
    Γⱼ∈ , _ = ∈-allTransitions⁻ tr′ xy∈′
    txoutΓⱼ = Txout≈ {Γⱼ′}{Γⱼ} x≈′
            $ Txout∈ {R = R′} (𝕣′ .ℝ.txout′) Γⱼ∈

  in
    ℍ[C-Advertise]⇒Txout {Γ = Γⱼ}{ad = ad} ℍ txoutΓⱼ

auth-commit∈⇒TxoutG : ∀ {Δ : List (Secret × Maybe ℕ)} →
  ∙ auth-commit⦅ A , ad , Δ ⦆ ∈ labels R
  ∙ ℝ R
    ──────────────────────────────────────
    Txout ad
auth-commit∈⇒TxoutG {A}{ad} {R} α∈ 𝕣 = auth-commit∈⇒Txout {A}{ad} {R} α∈ 𝕣 .proj₁
