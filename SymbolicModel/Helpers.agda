open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Setoid
open import Prelude.Membership
open import Prelude.Collections
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.InferenceRules
open import Prelude.Decidable

module SymbolicModel.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run         Participant Honest
  hiding ({-variables-} Γₜ; Γₜ′; Γₜ″; R′)
open import SymbolicModel.Collections Participant Honest
open import SymbolicModel.Mappings    Participant Honest
open import SymbolicModel.Accessors   Participant Honest

-- [BUG] See issue #5464
_≈ᶜ_ = _≈_ ⦃ Setoid-Cfg ⦄

-- Well-formed traces that additionally carry mappings.
data ℝ∗ : Run → Set where
  _∎⊣_✓ : ∀ {Γₜ} →

    ∙ ℾᵗ Γₜ
    → (init : Initial Γₜ) →
      ───────────────────
      ℝ∗ (Γₜ ∎⊣ init)

  _∷_⊣_✓ :
    ∀ Γₜ →
    ∙ ℝ∗ R
    → (λˢ : 𝕃 R Γₜ) →
      ───────────────────────
      ℝ∗ (Γₜ ∷ R ⊣ λˢ .proj₁)

ℝ∗-∅ˢ : ℝ∗ ∅ˢ
ℝ∗-∅ˢ = ℾᵗ-∅ᵗ ∎⊣ auto ✓

_∷_⊣≡_✓ :
  ∀ Γₜ →
  ∙ ℝ∗ R
  → (λˢ : 𝕃≡ R Γₜ) →
    ────────────────────────
    ℝ∗ (Γₜ ∷ R ⊣≡ λˢ .proj₁)
_∷_⊣≡_✓ {R} Γₜ 𝕣 𝕝≡ = Γₜ ∷ 𝕣 ⊣ 𝕃≡⇒𝕃 {R} 𝕝≡ ✓

ℝ∗⇒ℝ : ℝ∗ ⊆¹ ℝ
ℝ∗⇒ℝ {R} = λ where
  (ℽ ∎⊣ init ✓)  → ℝ-base {init = init} ℽ
  (_ ∷ 𝕣 ⊣ λˢ ✓) → ℝ-step (ℝ∗⇒ℝ 𝕣) λˢ

ℝ∗⇒ℾᵗ : ℝ∗ R → ℾᵗ (R .end)
ℝ∗⇒ℾᵗ (ℽ ∎⊣ _ ✓) = ℽ
ℝ∗⇒ℾᵗ (_∷_⊣_✓ {R} _ _ λˢ) = 𝕃⇒ℾᵗ {R} λˢ

ℝ∗⇒ℾ : ℝ∗ R → ℾ (R ∙cfg)
ℝ∗⇒ℾ = ℾᵗ⇒ℾ ∘ ℝ∗⇒ℾᵗ

-- lifting mappings from last configuration to enclosing runs
-- i.e. Γ →⦅ Txout ⟩ Γ′ ———→ R ⇒⟨ Txout ⦆ R′
LIFTˢ : ∀ (r : ℝ R) t α (t′ : Time) Γ (R≈ : R ≈⋯ Γ at t) Γ′ →
  ∙ Γ at t —[ α ]→ₜ Γ′ at t′
  → (∃Γ≈ : ∃ (_≈ᶜ Γ′)) →
  ∙ Γ →⦅ Txout ⦆ Γ′
  ∙ Γ →⦅ Sechash ⦆ Γ′
  ∙ Γ →⦅ 𝕂² ⦆ Γ′
    ────────────────────────
    𝕃 R (∃Γ≈ .proj₁ at t′)
LIFTˢ {R} r t α t′ Γ R≈@(_ , Γ≈) Γ′ Γ→Γ′ (Γ″ , Γ≈″) txout↝ sechash↝ κ↝
  = 𝕒 , [txout: txoutΓ′ ∣sechash: sechashΓ′ ∣κ: κΓ′ ]
  where
    open ℝ r; Γₜ = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′

    eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ
    eq = (refl , Γ≈″) , R≈

    𝕒 : 𝔸 R Γₜ″
    𝕒 = α , Γₜ , Γₜ′ , Γ→Γ′ , eq

    R′ = Γₜ″ ∷ R ⊣ 𝕒

    txoutΓ′ : Txout Γ′
    txoutΓ′ = txout↝ $ Txout≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)

    -- pv↝ :
    --   ∙ ValuePreserving  {Γ} txout′
    --   ∙ ValuePreserving↝ {Γ}{Γ′} txout↝
    --     ──────────────────────────────────
    --     ValuePreserving txoutΓ′
    -- pv↝ pv pvΓ
    --   = pvΓ (Txout≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
    --   ∘ ValuePreserving-Txout≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)
    --   ∘ {!!}

    sechashΓ′ : Sechash Γ′
    sechashΓ′ = sechash↝ $ Sechash≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ sechash′ $ namesˡ⦅end⦆⊆ R)

    κΓ′ : 𝕂² Γ′
    κΓ′ = κ↝ (𝕂²≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ κ′ $ ads⦅end⦆⊆ R))

ANCESTOR : ∀ {c Γ} →
  ∙ R ≈⋯ Γ at t
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
    ─────────────────────
    ∃ λ ad
    → Valid ad
    × ad ∈ advertisements R
    × c ⊆ subtermsᵃ′ ad
    × ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
ANCESTOR {R = R@(record {trace = _ , tr})} {Γ = Γ} R≈ c∈ =
  let ad , ∃H@(_ , _ , _ , _ , _ , _ , _ , ad↝c) = c∈≈⇒Ancestor {R}{Γ} R≈ c∈
      _ , vad , ad∈ = ℍ[C-Init]⇒∃ℍ[C-AuthInit] (R .init) tr (∃-weakenP tr proj₁ ∃H)
  in  ad , vad , ad∈ , h-sub∙↝∗ {ad} ad↝c , ∃H

-- lifting mapping from the current run to the original advertisement (needed to invoke the compiler)
LIFT₀ : ∀ (r : ℝ R) (t : Time) Γ (R≈ : R ≈⋯ Γ at t) ad →
  ∙ ` ad ∈ᶜ Γ
  ∙ nub-participants ad ⊆ committedParticipants ad Γ
    ─────────────────────────────────────────────────
    𝔾 ad
LIFT₀ {R} r t Γ R≈@(_ , Γ≈) ad ad∈ committedA = vad , txout₀ , sechash₀ , κ₀
  where
    open ℝ r

    ℍ-Ad = ad∈≈⇒ℍ {R}{Γ} R≈ ad∈

    vad : Valid ad
    vad = let _ , _ , _ , _ , _ , _ , _ , vad , _ = ℍ-Ad in vad

    txout₀ : Txout (ad .G)
    txout₀ =
      let
        Γᵢ′ , Γᵢ , _ , _ , xy∈ , (x≈ , _) , ℍ = ℍ-Ad

        Γᵢ∈ , _ = ∈-allTransitions⁻ (R ∙trace′) xy∈

        txoutΓᵢ : Txout Γᵢ
        txoutΓᵢ = Txout≈ {Γᵢ′}{Γᵢ} x≈
                $ Txout∈ {R = R} txout′ Γᵢ∈
      in
        ℍ[C-Advertise]⇒TxoutG {Γ = Γᵢ}{ad = ad} ℍ txoutΓᵢ

    sechash₀ : Sechash (ad .G)
    sechash₀ = ℍ[C-AuthCommit]∗⇒SechashG {ad = ad}
             $ committed⇒ℍ[C-AuthCommit]∗ {R}{Γ}{t}{ad} R≈ committedA sechash′

    κ₀ : 𝕂²′ ad
    κ₀ = weaken-↦ κ′ (ads⦅end⦆⊆ R ∘ ∈ads-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ R≈))
                     (∈-collect-++⁺ʳ (` ad) Γ ad∈Hon)
      where
        ad∈Hon : ad ∈ authorizedHonAds Γ
        ad∈Hon =
          let
            _ , _ , _ , _ , _ , _ , (_ , _ , honG , _) = ℍ-Ad
            honA = L.Any.lookup honG

            hon : honA ∈ Hon
            hon = L.Any.lookup-result honG

            honA∈ : honA ∈ nub-participants ad
            honA∈ = L.Mem.∈-lookup (L.Any.index honG)
          in
            committed⇒authAd hon {Γ = Γ} $ committedA honA∈

LIFTᶜ : ∀ (𝕣 : ℝ Rˢ) {ad c} →
  ∙ ∃[ Rˢ ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
    ─────────────────────────────
    𝔾 ad
LIFTᶜ {R} 𝕣 {ad} ∃H =
  let
    ∃R : ∃[ R ∋ʳ ∃ℍ[C-AuthInit]⦅_↝_⦆⦅ ad ⦆ ]
    ∃R = proj₁ $ ℍ[C-Init]⇒∃ℍ[C-AuthInit] (R .init) (R ∙trace′) $ ∃-weakenP (R ∙trace′) proj₁ ∃H

    x , x′ , _ , _ , xy∈ , (x≈ , _) , _ , _ , _ , _ , Γ≡ , _ , p⊆′ , _  = ∃R

    ad∈ : ` ad ∈ᶜ x
    ad∈ = ∈ᶜ-resp-≈ {x′}{x} (↭-sym x≈)
        $ subst (` ad ∈ᶜ_) (sym Γ≡) (here refl)

    p⊆ : (ad .G ∙partG) ⊆ committedParticipants ad x
    p⊆ = L.Perm.∈-resp-↭ (collectFromList↭ (∣committedParticipants∣.go ad .collect) (↭-sym x≈))
       ∘ p⊆′

    tr = R ∙trace′
    tᵢ , _ , xy∈ᵗ = ×∈⇒×∈ᵗ tr xy∈
    tr′      = splitTraceˡ tr xy∈ᵗ
    R′       = splitRunˡ R xy∈ᵗ

    𝕣′ : ℝ R′
    𝕣′ = ℝ⊆ xy∈ᵗ 𝕣

    R≈′ : R′ ≈⋯ x at tᵢ
    R≈′ = splitRunˡ-≈⋯ R xy∈ᵗ
  in
    LIFT₀ 𝕣′ tᵢ x R≈′ ad ad∈ p⊆

ad∈⇒TxoutG :
  ∙ ` ad ∈ᶜ Γ
  ∙ R ≈⋯ Γ at t
  ∙ Txout R
    ───────────
    Txout ad
ad∈⇒TxoutG {ad}{Γ}{R@(record {trace = _ , tr})} ad∈ R≈ txout =
  let
    Γᵢ′ , Γᵢ , _ , _ , xy∈ , (x≈ , _) , ℍ = ad∈≈⇒ℍ {R}{Γ} R≈ ad∈
    Γᵢ∈ , _ = ∈-allTransitions⁻ tr xy∈
    txoutΓᵢ = Txout≈ {Γᵢ′}{Γᵢ} x≈
            $ Txout∈ {R = R} txout Γᵢ∈
  in
    ℍ[C-Advertise]⇒TxoutG {Γ = Γᵢ}{ad = ad} ℍ txoutΓᵢ

auth-commit∈⇒TxoutG : ∀ {Δ : List (Secret × Maybe ℕ)} →
  ∙ auth-commit⦅ A , ad , Δ ⦆ ∈ labels R
  ∙ ℝ R
    ──────────────────────────────────────
    Txout ad
auth-commit∈⇒TxoutG {A}{ad} {R@(record {trace = _ , tr})} α∈ 𝕣 =
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
    ℍ[C-Advertise]⇒TxoutG {Γ = Γⱼ}{ad = ad} ℍ txoutΓⱼ
