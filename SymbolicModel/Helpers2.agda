{-# OPTIONS -v profile:7 #-}
open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open L.Mem using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Validity

open import Prelude.Traces
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Setoid
open import Prelude.Coercions

open import Bitcoin.Crypto
open import Bitcoin.Tx

module SymbolicModel.Helpers2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest as S
  hiding ( _∎; begin_
         ; {-variables-} g; c; as; vs; xs; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; R′; Δ )
open import SymbolicModel.Collections Participant Honest

𝕃 : S.Run → Cfgᵗ → Set
𝕃 R Γ = Σ[ 𝕒 ∈ 𝔸 R Γ ] ℝ (Γ ∷ R ⊣ 𝕒)

-- lifting mappings from last configuration to enclosing runs
-- i.e. Γ →⦅ Txout ⟩ Γ′ ———→ R ⇒⟨ Txout ⦆ R′
LIFTˢ : ∀ (r : ℝ R) t α t′ Γ (R≈ : R ≈⋯ Γ at t) Γ′
  → Γ at t —[ α ]→ₜ Γ′ at t′
  → (∃Γ≈ : ∃ (_≈ᶜ Γ′))
  → Γ →⦅ Txout ⦆ Γ′
  → Γ →⦅ Sechash ⦆ Γ′
  → Γ →⦅ 𝕂² ⦆ Γ′
    --——————————————————––––––———–
  → 𝕃 R (∃Γ≈ .proj₁ at t′)
LIFTˢ {R} r t α t′ Γ R≈@(_ , Γ≈) Γ′ Γ→Γ′ (Γ″ , Γ≈″) txout↝ sechash↝ κ↝
  = 𝕒 , [txout: txout ∣sechash: sechash ∣κ: κ ]
  where
    open ℝ r; Γₜ = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′

    eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ
    eq = (refl , Γ≈″) , R≈

    𝕒 : 𝔸 R Γₜ″
    𝕒 = α , Γₜ , Γₜ′ , Γ→Γ′ , eq

    R′ = Γₜ″ ∷ R ⊣ 𝕒

    txoutΓ′ : Txout Γ′
    txoutΓ′ = txout↝ $ Txout≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)

    sechashΓ′ : Sechash Γ′
    sechashΓ′ = sechash↝ $ Sechash≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ sechash′ $ namesˡ⦅end⦆⊆ R)

    txout : Txout R′
    txout = txout∷ {R = R} Γ→Γ′ eq txoutΓ′ txout′

    sechash : Sechash R′
    sechash = sechash∷ {R = R} Γ→Γ′ eq sechashΓ′ sechash′

    κ : 𝕂² R′
    κ {ad} ad∈ with ads∈-⊎ {α}{Γₜ′}{Γₜ″}{R}{ad}{Γₜ} Γ→Γ′ eq ad∈
    ... | inj₁ ad∈R  = κ′ ad∈R
    ... | inj₂ ad∈Γ″ = κ↝ (𝕂²≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ κ′ $ ads⦅end⦆⊆ R))
                            (∈ads-resp-≈ ad {Γ″}{Γ′} Γ≈″ ad∈Γ″)

ANCESTOR : ∀ {c Γ}
  → R ≈⋯ Γ at t
  → ⟨ c , v ⟩at x ∈ᶜ Γ
    --————————————————————
  → ∃ λ ad
    → Valid ad
    × ad ∈ advertisements R
    × c ⊆ subtermsᵃ′ ad
    × ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
ANCESTOR {R = R@(record {trace = _ , tr})} {Γ = Γ} R≈ c∈ =
  let ad , ∃H@(_ , _ , _ , _ , _ , _ , _ , ad↝c) = c∈≈⇒Ancestor {R}{Γ} R≈ c∈
      _ , vad , ad∈ = ℍ[C-Init]⇒∃ℍ[C-AuthInit] (R .init) tr (∃-weakenP tr proj₁ ∃H)
  in  ad , vad , ad∈ , h-sub∙↝∗ {ad} ad↝c , ∃H

-- lifting mapping from the current run to the original advertisement (needed to invoke the compiler)
LIFT₀ : ∀ (r : ℝ R) (t : Time)
  Γ (R≈ : R ≈⋯ Γ at t) ad
  → ` ad ∈ᶜ Γ
  → nub-participants ad ⊆ committedParticipants ad Γ
  → 𝔾 ad
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
        txoutΓᵢ = Txout≈ {x = Γᵢ′}{Γᵢ} x≈
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

LIFTᶜ : ∀ (𝕣 : ℝ Rˢ) {ad c}
  → ∃[ Rˢ ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
    --————————————————————————————
  → 𝔾 ad
LIFTᶜ {R} 𝕣 {ad} ∃H =
  let
    ∃R : ∃[ R ∋ʳ ∃ℍ[C-AuthInit]⦅_↝_⦆⦅ ad ⦆ ]
    ∃R = proj₁ $ ℍ[C-Init]⇒∃ℍ[C-AuthInit] (R .init) (R ∙trace′) $ ∃-weakenP (R ∙trace′) proj₁ ∃H

    x , x′ , _ , _ , xy∈ , (x≈ , _) , _ , _ , _ , _ , Γ≡ , _ , p⊆′ , _  = ∃R

    ad∈ : ` ad ∈ᶜ x
    ad∈ = ∈ᶜ-resp-≈ {x′}{x} (↭-sym x≈)
        $ subst (` ad ∈ᶜ_) (sym Γ≡) (here refl)

    p⊆ : (ad .G ∙partG) ⊆ committedParticipants ad x
    p⊆ = L.Perm.∈-resp-↭ (collectFromList↭ (∣committedParticipants∣.go ad .collect) (↭-sym x≈)) ∘ p⊆′

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

-- Helpers for coherence, in order not to over-complicate the constructor definitions for `_~₁₁_`.
-- Also we need the complete power of rewrites/with that let-only expressions in constructors do not give us.
-- ∙ each module corresponds to an inductive case for Coherence
-- ∙ all definitions should be private, except two lifting functions:
--   ∘ λˢ : providing updated mappings for the symbolic run
--   ∘ Liftᶜ : providing mappings for invoking the compiler (optional)
module _ (𝕣 : ℝ R) t α t′ where
  open ℝ 𝕣

  -- [4]
  module _ ad Γ₀ (ds : List DepositRef) v z where
    private
      partG = ad .G ∙partG
      -- [BUG] cannot get this to work here without explicitly passing ⦃ HPᵖ ⦄
      -- [WORKAROUND1] give it as module parameters (forgetting the fact that it's computed out of `g`
      -- [WORKAROUND2] instantiate and give non-instance version _∙partG

      Γ₁ = ` ad ∣ Γ₀
      Γ₂ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) (ds)
      Γ₃ = || map (_auth[ ♯▷ ad ]) partG
      Γ  = Γ₁ ∣ Γ₂ ∣ Γ₃
      Γ′ = ⟨ ad .C , v ⟩at z ∣ Γ₀
    module H₄ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where abstract
      private
        committedA : partG ⊆ committedParticipants ad Γ
        committedA {p} p∈ = ∈-collect-++⁺ʳ (Γ₁ ∣ Γ₂) Γ₃ ⦃ ∣committedParticipants∣.go ad ⦄ p∈′
          where p∈′ : p ∈ committedParticipants ad Γ₃
                p∈′ rewrite committedPartG≡ {ad} partG = p∈
      Liftᶜ : 𝔾 ad
      Liftᶜ = LIFT₀ 𝕣 t Γ R≈ ad (here refl) committedA

      module H₄′ (tx : TxInput′) where -- abstract -- **wrong** choice
        private
          h₀ : ∀ ps → Null $ namesʳ (|| map (_auth[ ♯▷ ad ]) ps)
          h₀ [] = refl
          h₀ (_ ∷ []) = refl
          h₀ (_ ∷ ps@(_ ∷ _)) = h₀ ps

          h₀′ : ∀ (ds : List DepositRef) →
            namesʳ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds) ≡ map (proj₂ ∘ proj₂) ds
          h₀′ [] = refl
          h₀′ (_ ∷ []) = refl
          h₀′ ((Aᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) =
            begin
              namesʳ ((⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ∣ Δ)
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) Δ ⟩
              namesʳ (⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ++ namesʳ Δ
            ≡⟨ cong (_++ namesʳ Δ) (mapMaybe∘collectFromBase-++ isInj₂ (⟨ Aᵢ has vᵢ ⟩at xᵢ) (Aᵢ auth[ xᵢ ▷ˢ ad ])) ⟩
              (xᵢ ∷ namesʳ (Aᵢ auth[ xᵢ ▷ˢ ad ])) ++ namesʳ Δ
            ≡⟨ cong (λ x → (xᵢ ∷ x) ++ namesʳ Δ) (L.++-identityʳ _) ⟩
              xᵢ ∷ namesʳ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds)
            ≡⟨ cong (xᵢ ∷_) (h₀′ ds) ⟩
              xᵢ ∷ map (proj₂ ∘ proj₂) ds
            ∎ where open ≡-Reasoning
                    Δ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds

          h₁ : ∀ (xs : List DepositRef) →
            Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) xs)
          h₁ [] = refl
          h₁ (_ ∷ []) = refl
          h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

          h₂ : ∀ xs → Null $ namesˡ (|| map (_auth[ ♯▷ ad ]) xs)
          h₂ [] = refl
          h₂ (_ ∷ []) = refl
          h₂ (_ ∷ xs@(_ ∷ _)) = h₂ xs

          h₁′ : ∀ (xs : List DepositRef) →
            Null $ advertisements (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) xs)
          h₁′ [] = refl
          h₁′ (_ ∷ []) = refl
          h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

          namesʳ≡₀ : namesʳ Γ ≡ namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
          namesʳ≡₀ =
            begin
              namesʳ Γ
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (Γ₁ ∣ Γ₂) Γ₃ ⟩
              namesʳ (Γ₁ ∣ Γ₂) ++ namesʳ Γ₃
            ≡⟨ cong (namesʳ (Γ₁ ∣ Γ₂) ++_) (h₀ partG) ⟩
              namesʳ (Γ₁ ∣ Γ₂) ++ []
            ≡⟨ L.++-identityʳ _ ⟩
              namesʳ (Γ₁ ∣ Γ₂)
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ₁ Γ₂ ⟩
              namesʳ Γ₁ ++ namesʳ Γ₂
            ≡⟨ cong (_++ namesʳ Γ₂) (mapMaybe∘collectFromBase-++ isInj₂ (` ad) Γ₀) ⟩
              namesʳ Γ₀ ++ namesʳ Γ₂
            ≡⟨ cong (namesʳ Γ₀ ++_) (h₀′ ds) ⟩
              namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
            ∎ where open ≡-Reasoning

          namesˡ≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
          namesˡ≡ = sym $
            begin namesˡ Γ                      ≡⟨⟩
                  namesˡ (Γ₁ ∣ Γ₂ ∣ Γ₃)         ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ (Γ₁ ∣ Γ₂) Γ₃ ⟩
                  namesˡ (Γ₁ ∣ Γ₂) ++ namesˡ Γ₃ ≡⟨ cong (namesˡ (Γ₁ ∣ Γ₂)  ++_) (h₂ partG) ⟩
                  namesˡ (Γ₁ ∣ Γ₂) ++ []        ≡⟨ L.++-identityʳ _ ⟩
                  namesˡ (Γ₁ ∣ Γ₂)              ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ Γ₁ Γ₂ ⟩
                  namesˡ Γ₁ ++ namesˡ Γ₂        ≡⟨ cong (namesˡ Γ₁ ++_) (h₁ ds) ⟩
                  namesˡ Γ₁ ++ []               ≡⟨ L.++-identityʳ _ ⟩
                  namesˡ Γ₁                     ≡⟨⟩
                  namesˡ Γ′                     ∎ where open ≡-Reasoning

          ads⊆′ : Γ′ ⊆⦅ advertisements ⦆ Γ
          ads⊆′ = begin advertisements Γ′ ≡⟨⟩
                        advertisements Γ₀ ⊆⟨ ∈-collect-++⁺ˡ (Γ₁ ∣ Γ₂) Γ₃ ∘ ∈-collect-++⁺ˡ Γ₁ Γ₂ ⟩
                        advertisements Γ  ∎ where open ⊆-Reasoning Advertisement

          sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
          sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

          κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
          κ↝ κ′ = weaken-↦ κ′ ads⊆′

          txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝ txout′ rewrite namesʳ≡₀ = cons-↦ z tx $ weaken-↦ txout′ ∈-++⁺ˡ
        abstract -- **correct** choice
          λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
          λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
