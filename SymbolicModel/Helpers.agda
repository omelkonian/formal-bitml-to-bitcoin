open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Setoid
open import Prelude.Membership
open import Prelude.Lists.Collections
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.InferenceRules

open import BitML.BasicTypes using (⋯)

module SymbolicModel.Helpers (⋯ : ⋯) (let open ⋯ ⋯) where

open import Compiler.Mappings ⋯
open import SymbolicModel.Run ⋯
  hiding ({-variables-} Γₜ; Γₜ′; Γₜ″; R′)
open import SymbolicModel.Mappings ⋯
open import SymbolicModel.Properties ⋯

-- lifting mapping from the current run to the original advertisement
-- (needed to invoke the compiler)
LIFT₀ : ∀ (r : ℝ R) (t : Time) Γ (R≈ : R ≈⋯ Γ at t) ad →
  ∙ ` ad ∈ᶜ Γ
  ∙ nub-participants ad ⊆ committedParticipants ad Γ
    ─────────────────────────────────────────────────
    𝔾 ad
LIFT₀ {R} r t Γ R≈@(_ , Γ≈) ad ad∈ committedA = vad , txout₀ , sechash₀ , κ₀
  where
  module _
    (let Γᵢ′ , Γᵢ , _ , _ , xy∈ , (x≈ , _) , ℍ = ad∈≈⇒ℍ {R}{Γ} R≈ ad∈)
    (let _ , $vad , honG , _ = ℍ)
    where
    open ℝ r

    vad : Valid ad
    vad = $vad

    txout₀ : Txout (ad .G)
    txout₀ =
      let
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
    κ₀ =
      let
        ad∈Hon : ad ∈ authorizedHonAds Γ
        ad∈Hon = committed⇒authAd (L.Any.lookup-result honG) {Γ = Γ}
               $ committedA (L.Mem.∈-lookup $ L.Any.index honG)
      in
        weaken-↦ κ′ (ads⦅end⦆⊆ R ∘ ∈ads-resp-≈ _ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂))
          $ ∈-collect-++⁺ʳ (` ad) Γ ad∈Hon

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
