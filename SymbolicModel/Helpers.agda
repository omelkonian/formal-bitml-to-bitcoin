-- {-# OPTIONS --auto-inline #-}
-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open L.Mem using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open L.Perm using (Any-resp-↭; ∈-resp-↭)
open import Prelude.Lists.PermutationsMeta using (↭-sym∘↭-reflexive)
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
open import Prelude.InferenceRules
open import Prelude.Irrelevance

open import Bitcoin.Crypto
open import Bitcoin.Tx
open import ComputationalModel.Accessors

module SymbolicModel.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest as S
  hiding ( _∎; begin_
         ; {-variables-} g; c; as; vs; xs; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; R′; Δ )
open import SymbolicModel.Accessors Participant Honest
open import SymbolicModel.Collections Participant Honest
open import SymbolicModel.Mappings Participant Honest
open import SymbolicModel.ValuePreservation Participant Honest

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

ℝ∗⇒ℝ : ℝ∗ ⊆¹ ℝ
ℝ∗⇒ℝ {R} = λ where
  (ℽ ∎⊣ init ✓)  → ℝ-base {init = init} ℽ
  (_ ∷ 𝕣 ⊣ λˢ ✓) → ℝ-step (ℝ∗⇒ℝ 𝕣) λˢ

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
    p⊆ = ∈-resp-↭ (collectFromList↭ (∣committedParticipants∣.go ad .collect) (↭-sym x≈)) ∘ p⊆′

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

  -- [1]
  module _ Γ (R≈ : R ≈⋯ Γ at t) ad where
    private Γ′ = ` ad ∣ Γ
    module H₁ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        Γ″ = ∃Γ≈ .proj₁
        Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ
        Γₜ  = Γ at t
        Γₜ′ = Γ′ at t′
        Γₜ″ = Γ″ at t′

        $λˢ : 𝕃 R Γₜ″
        $λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

        𝕒  = $λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 $λˢ

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈

        namesʳ↭ : R .end ↭⦅ namesʳ ⦆ R′ .end
        namesʳ↭ = ↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                          (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))

        txoutΓ : Txout (R .end)
        txoutΓ = 𝕣 ∙txoutEnd_

        txoutΓ′≈ : Txout (R′ .end)
        txoutΓ′≈ = permute-↦ namesʳ↭ txoutΓ

        txoutΓ′ : Txout Γ′
        txoutΓ′ = Txout≈ {R′ ∙cfg}{Γ′} Γ≈ txoutΓ′≈

        txoutR′ : Txout R′
        txoutR′ = txout∷ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′

        txoutΓₜ′ : Txout (Γ′ at t′)
        txoutΓₜ′ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ

        x∈⇒ : namesʳ (R .end) ⊆ namesʳ (R′ .end)
        x∈⇒ = ∈-resp-↭ namesʳ↭

        open ≡-Reasoning

        txoutEnd≡ : ∀ {x : Id} (x∈ : x ∈ namesʳ (R .end))
          → 𝕣′ ∙txoutEnd (x∈⇒ x∈) ≡ 𝕣 ∙txoutEnd x∈
        txoutEnd≡ {x} x∈ =
          begin
            𝕣′ ∙txoutEnd (x∈⇒ x∈)
          ≡⟨⟩
            𝕣′ ∙txout (namesʳ⦅end⦆⊆ R′ $ x∈⇒ x∈)
          ≡⟨⟩
            (txout∷ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓₜ′ txout′)
            (namesʳ⦅end⦆⊆ R′ $ x∈⇒ x∈)
          ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓₜ′ txout′
               $ ∈-resp-↭ namesʳ↭ x∈ ⟩
            ( Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ R≈′ .proj₂)
            $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ
            ) (x∈⇒ x∈)
          ≡⟨⟩
            ( permute-↦ (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ}          $ R≈ .proj₂)
                                 (≈⇒namesʳ↭ {Γₜ′ .cfg}{Γₜ″ .cfg} $ ↭-sym Γ≈))
            $ txoutΓ
            ) (x∈⇒ x∈)
          ≡⟨⟩
            ( permute-↦ (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ}          $ R≈ .proj₂)
                                 (≈⇒namesʳ↭ {Γₜ′ .cfg}{Γₜ″ .cfg} $ ↭-sym Γ≈))
            $ txoutΓ
            ) (∈-resp-↭ namesʳ↭ x∈)
          ≡⟨ cong (λ ◆ →
            ( permute-↦ (↭-trans (≈⇒namesʳ↭ {R ∙cfg} {Γ} $ R≈ .proj₂)
                                 (≈⇒namesʳ↭ {Γₜ′ .cfg} {Γₜ″ .cfg} $ ↭-sym Γ≈))
            $ txoutΓ
            ) (∈-resp-↭ ◆ x∈)) (sym $ L.Perm.↭-sym-involutive namesʳ↭) ⟩
            ( permute-↦ (↭-sym namesʳ↭)
            $ permute-↦ (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ}          $ R≈ .proj₂)
                                 (≈⇒namesʳ↭ {Γₜ′ .cfg}{Γₜ″ .cfg} $ ↭-sym Γ≈))
            $ txoutΓ
            ) x∈
          ≡⟨⟩
            ( permute-↦ (↭-trans (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ}          $ R≈ .proj₂)
                                          (≈⇒namesʳ↭ {Γₜ′ .cfg}{Γₜ″ .cfg} $ ↭-sym Γ≈))
                                 (↭-sym namesʳ↭))
            $ txoutΓ
            ) x∈
          ≡⟨⟩
            permute-↦ (↭-trans namesʳ↭ (↭-sym namesʳ↭)) txoutΓ x∈
          ≡⟨ permute-↦∘permute-↦˘ namesʳ↭ txoutΓ x∈ ⟩
            txoutΓ x∈
          ≡⟨⟩
            𝕣 ∙txoutEnd x∈
          ∎
{-
        module _ {c v x} where

          c∈Γ⇐ : ⟨ c , v ⟩at x ∈ᶜ Γ′
                → ⟨ c , v ⟩at x ∈ᶜ Γ
          c∈Γ⇐ (there c∈) = c∈

          c∈⇒x∈∘Γ⊆ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ′) →
            ( c∈⇒x∈ Γ
            ∘ c∈Γ⇐
            ) c∈
            ≡ c∈⇒x∈ Γ′ c∈
          c∈⇒x∈∘Γ⊆ (there _) = refl

          c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
              → R  ≈⋯ ⟨ c , v ⟩at x ⋯
          c∈⇐ = ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
              ∘ c∈Γ⇐
              ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈

          txoutEndC≡ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″) →
            𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC (c∈⇐ c∈)
          txoutEndC≡ c∈ =
            begin
              𝕣′ ∙txoutC c∈
            ≡⟨⟩
              𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
            ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
              𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
              𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨⟩
              𝕣 ∙txoutC (c∈⇐ c∈)
            ∎ where
              H : (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″)
                → x∈⇒ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
                ≡ c∈⇒x∈ (R′ ∙cfg) c∈
              {- i.e. the following diagram commutes

                  x ∈                      x ∈
                  ids Γ ——————— x∈⇒ —————→ ids (` ad) ++ ids Γ
                    ↑                    ⇑
                    ∣                    ∥
                    ∣                    ∥
                  c∈⇒x∈                c∈⇒x∈
                    ∣                    ∥
                    ∣                    ∥
                    Γ ←—————— c∈⇐ —————— Γ′ ≈ ` ad ∣ Γ
              -}
              H c∈ =
                begin
                  x∈⇒ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
                ≡⟨⟩
                  ( x∈⇒
                  ∘ c∈⇒x∈ (R ∙cfg)
                  ∘ c∈⇐
                  ) c∈
                ≡⟨⟩
                  ( ∈-resp-↭ namesʳ↭
                  ∘ c∈⇒x∈ (R ∙cfg)
                  ∘ c∈⇐
                  ) c∈
                ≡⟨⟩
                  ( ∈-resp-↭ (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                                      (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈)))
                  ∘ c∈⇒x∈ (R ∙cfg)
                  ∘ c∈⇐
                  ) c∈
                ≡⟨⟩
                  ( ∈-resp-↭ (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                                      (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈)))
                  ∘ c∈⇒x∈ (R ∙cfg)
                  ∘ ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
                  ∘ c∈Γ⇐
                  ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} (∃Γ≈ .proj₂)
                  ) c∈
                ≡⟨⟩
                  ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ″} (↭-sym Γ≈))
                  ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                  ∘ c∈⇒x∈ (R ∙cfg)
                  ∘ ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
                  ∘ c∈Γ⇐
                  ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈
                  ) c∈
                ≡⟨ cong (∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ″} (↭-sym Γ≈)))
                      $ ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈˘ Γ (R ∙cfg) (R≈ .proj₂)
                          (c∈Γ⇐ $ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈) ⟩
                  ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈))
                  ∘ c∈⇒x∈ Γ ∘ c∈Γ⇐
                  ∘ ∈ᶜ-resp-≈ {R′ ∙cfg}{Γ′} Γ≈
                  ) c∈
                ≡⟨ cong (∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈)))
                      $ c∈⇒x∈∘Γ⊆ (∈ᶜ-resp-≈ {R′ ∙cfg}{Γ′} Γ≈ c∈) ⟩
                  ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈))
                  ∘ c∈⇒x∈ Γ′
                  ∘ ∈ᶜ-resp-≈ {R′ ∙cfg}{Γ′} Γ≈
                  ) c∈
                ≡⟨ ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈ (R′ ∙cfg) Γ′ Γ≈ c∈ ⟩
                  c∈⇒x∈ (R′ ∙cfg) c∈
                ∎
-}
      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = $λˢ

      abstract
        -- value-preserving⇒ :
        --   ValuePreservingʳᶜ 𝕣
        --   ────────────────────
        --   ValuePreservingʳᶜ 𝕣′
        -- value-preserving⇒ IH c∈ = trans (cong _∙value (txoutEndC≡ _)) (IH (c∈⇐ _))
        value-preserving⇒ :
          ValuePreservingʳ 𝕣
          ───────────────────
          ValuePreservingʳ 𝕣′
        -- value-preserving⇒ pv-txout x∈ =
        --   begin
        --     (𝕣′ ∙txoutEnd x∈) ∙value
        --   ≡⟨⟩
        --     (𝕣′ ∙txout (namesʳ⦅end⦆⊆ R′ x∈)) ∙value
        --   -- ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓₜ′ txout′ x∈ ⟩
        --   --   ( Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ R≈′ .proj₂)
        --   --   $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ
        --   --   ) x∈
        --   -- ≡⟨⟩
        --   --   ( permute-↦ (↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ}          $ R≈ .proj₂)
        --   --                        (≈⇒namesʳ↭ {Γₜ′ .cfg}{Γₜ″ .cfg} $ ↭-sym Γ≈))
        --   --   $ txoutΓ
        --   --   ) x∈
        --   ≡⟨ {!!} ⟩
        --     (Γ″ , x∈) ∙value
        --   ∎
        value-preserving⇒ pv-txout = pv-txout′
          where
          -- pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
          -- pv-txoutΓ′ = pv-txout

          txoutΓ″ : Txout Γ″
          txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

          pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
          pv-txoutΓ″ = {!!} -- ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

          pv-txout′ : ValuePreservingʳ 𝕣′
          -- pv-txout′ = {!pv-permute-↦ {R ∙cfg}{R′ ∙cfg} txoutΓ namesʳ↭ ? pv-txout!}
          pv-txout′ x∈ =
            begin
              (𝕣′ ∙txoutEnd x∈) ∙value
            -- ≡⟨ cong _∙value
            --       $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
            --   (txoutΓ″ x∈) ∙value
            -- ≡⟨ pv-txoutΓ″ _ ⟩
            ≡⟨ {!!} ⟩
              (Γ″ , x∈) ∙value
            ∎


  -- [2]
  module _ Γ (R≈ : R ≈⋯ Γ at t) B A ad (Δ : List (Secret × Maybe ℕ)) where
    private
      Γ′ = Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ]
      as = proj₁ $ unzip Δ
    module H₂ (sechash⁺ : as ↦ ℤ) (k⃗ : 𝕂²′ ad) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        open ≡-Reasoning

        namesʳ≡ : Γ′ ≡⦅ namesʳ ⦆ Γ
        namesʳ≡ =
          begin
            namesʳ Γ′
          ≡⟨⟩
            namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ])
          ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ]) ⟩
            namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ namesʳ (A auth[ ♯▷ ad ])
          ≡⟨⟩
            namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ []
          ≡⟨ L.++-identityʳ _ ⟩
            namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
            namesʳ Γ ++ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨ cong (namesʳ Γ ++_) (hʳ Δ) ⟩
            namesʳ Γ ++ []
          ≡⟨ L.++-identityʳ _ ⟩
            namesʳ Γ
          ∎ where
            hʳ : ∀ Δ → Null $ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
            hʳ [] = refl
            hʳ (_ ∷ []) = refl
            hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _

        namesˡ≡ : namesˡ Γ′ ≡ namesˡ Γ ++ as
        namesˡ≡ =
          begin
            namesˡ Γ′
          ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ]) ⟩
            namesˡ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ []
          ≡⟨ L.++-identityʳ _ ⟩
            namesˡ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
            namesˡ Γ ++ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨ cong (namesˡ Γ ++_) (hˡ Δ) ⟩
            namesˡ Γ ++ as
          ∎ where
            hˡ : ∀ Δ → namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) ≡ proj₁ (unzip Δ)
            hˡ [] = refl
            hˡ (_ ∷ []) = refl
            hˡ ((s , m) ∷ Δ@(_ ∷ _)) =
              begin
                namesˡ (⟨ B ∶ s ♯ m ⟩ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
              ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ ⟨ B ∶ s ♯ m ⟩ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
                namesˡ ⟨ B ∶ s ♯ m ⟩ ++ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
              ≡⟨⟩
                s ∷ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
              ≡⟨ cong (s ∷_) (hˡ Δ) ⟩
                s ∷ proj₁ (unzip Δ)
              ∎

        hᵃ : ∀ Δ → Null $ advertisements (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        hᵃ [] = refl
        hᵃ (_ ∷ []) = refl
        hᵃ (_ ∷ Δ@(_ ∷ _)) rewrite hᵃ Δ = L.++-identityʳ _

        ads≡ : advertisements Γ′ ≡ advertisements Γ ++ advertisements (A auth[ ♯▷ ad ])
        ads≡ rewrite collectFromBase-++ {X = Advertisement} (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ])
                    | collectFromBase-++ {X = Advertisement} Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
                    | hᵃ Δ
                    | L.++-identityʳ (advertisements Γ)
                    = refl

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ = lift Γ —⟨ namesʳ ⟩— Γ′ ⊣ namesʳ≡

        sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ = extend-↦ (↭-reflexive namesˡ≡) sechash′ sechash⁺

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ = extend-↦ (↭-reflexive ads≡) κ′ κ″
          where
            κ″ : advertisements (A auth[ ♯▷ ad ]) ↦′ 𝕂²′
            κ″ x∈ with does (A ∈? Hon) | x∈
            ... | true  | here refl = k⃗
            ... | false | ()

        --

        Γ″ = ∃Γ≈ .proj₁
        Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ
        Γₜ  = Γ at t
        Γₜ′ = Γ′ at t′
        Γₜ″ = Γ″ at t′

        $λˢ : 𝕃 R Γₜ″
        $λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

        𝕒  = $λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 $λˢ

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈

        namesʳ↭ : R .end ↭⦅ namesʳ ⦆ R′ .end
        namesʳ↭ = ↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                $ ↭-trans (↭-reflexive $ sym namesʳ≡)
                          (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))

        txoutΓ : Txout (R .end)
        txoutΓ = 𝕣 ∙txoutEnd_

        txoutΓ′ : Txout Γ′
        txoutΓ′ = txout↝ $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)

        x∈⇒ : namesʳ (R .end) ⊆ namesʳ (R′ .end)
        x∈⇒ = ∈-resp-↭ namesʳ↭

        txoutEnd≡ : ∀ {x : Id} (x∈ : x ∈ namesʳ (R .end))
          → 𝕣′ ∙txoutEnd (x∈⇒ x∈) ≡ 𝕣 ∙txoutEnd x∈
        txoutEnd≡ {x} x∈ =
          begin
            𝕣′ ∙txoutEnd (x∈⇒ x∈)
          ≡⟨⟩
            𝕣′ ∙txout (namesʳ⦅end⦆⊆ R′ $ x∈⇒ x∈)
          ≡⟨⟩
            ( txout∷ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′
            ∘ namesʳ⦅end⦆⊆ R′
            ∘ x∈⇒
            ) x∈
          ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ (x∈⇒ x∈) ⟩
            ( Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ R≈′ .proj₂) txoutΓ′
            ∘ x∈⇒
            ) x∈
          ≡⟨⟩
            ( Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ R≈′ .proj₂)
                ( txout↝
                $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ
                )
            ∘ x∈⇒
            ) x∈
          ≡⟨⟩
            ( Txout≈ {Γ′}{Γ″} (↭-sym $ R≈′ .proj₂)
                ( txout↝
                $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ
                )
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))
            ∘ ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
            ) x∈
          ≡⟨ Txout≗ {Γ′}{Γ″} (↭-sym $ R≈′ .proj₂) (txout↝ $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ)
               ( ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
               $ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂)) x∈) ⟩
            ( txout↝ (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ)
            ∘ ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
            ) x∈
          ≡⟨ (lift≗ Γ —⟨ namesʳ ⟩— Γ′ ⊣ namesʳ≡)
               (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ)
               (∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂)) x∈) ⟩
            ( Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
            ) x∈
          ≡⟨ Txout≗ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ x∈ ⟩
            txoutΓ x∈
          ≡⟨⟩
            𝕣 ∙txoutEnd x∈
          ∎

        Γ₁ = || map (uncurry ⟨ B ∶_♯_⟩) Δ
        Γ₂ = A auth[ ♯▷ ad ]

        postulate
          ∈-resp-↭∘∈-++⁺ˡ∘∈-++⁺ˡ : ∀ {A : Set} {x : A} {xs ys zs : List A} →
            (xs≡ : (xs ++ ys) ++ zs ≡ xs)
            (x∈ : x ∈ xs) →
            --————————————————————————————————
            ( ∈-resp-↭ (↭-reflexive xs≡)
            ∘ ∈-++⁺ˡ {xs = (xs ++ ys)}{zs}
            ∘ ∈-++⁺ˡ {xs = xs}{ys}
            ) x∈
            ≡ x∈

        ∈-resp-↭∘∈-ids-++⁺ˡ : ∀ (x∈ : x ∈ ids Γ) →
          ( ∈-resp-↭ (↭-reflexive namesʳ≡)
          ∘ ∈-ids-++⁺ˡ (Γ ∣ Γ₁) Γ₂
          ∘ ∈-ids-++⁺ˡ Γ Γ₁
          ) x∈
          ≡ x∈
        ∈-resp-↭∘∈-ids-++⁺ˡ x∈
          with eq ← namesʳ≡
          rewrite ids-++ (Γ ∣ Γ₁) Γ₂
                | ids-++ Γ Γ₁
                = ∈-resp-↭∘∈-++⁺ˡ∘∈-++⁺ˡ eq x∈

        module _ {c v x} where
          c∈Γ⇐ : ⟨ c , v ⟩at x ∈ᶜ Γ′
               → ⟨ c , v ⟩at x ∈ᶜ Γ
          c∈Γ⇐ c∈
            with destruct-∈ᶜ-++ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ]) c∈
          ... | inj₂ (here () , _)
          ... | inj₁ (c∈ , _)
            with destruct-∈ᶜ-++ Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) c∈
          ... | inj₁ (c∈Γ , _) = c∈Γ
          ... | inj₂ (c∈Δ , _) = ⊥-elim $ ∉ᶜ-|| (λ where (here ())) Δ c∈Δ

          c∈⇒x∈∘c∈Γ⇐ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ′)
            --————————————————————————————————
            → ( c∈⇒x∈ Γ   -- x ∈ ids Γ
              ∘ c∈Γ⇐      -- ⟨C,v⟩ₓ ∈ᶜ Γ
              ) c∈        -- ⟨C,v⟩ₓ ∈ᶜ Γ′
            ≡ ( ∈-resp-↭ (↭-reflexive namesʳ≡) -- x ∈ ids Γ
              ∘ c∈⇒x∈ Γ′                       -- x ∈ ids Γ′
              ) c∈                             -- ⟨C,v⟩ₓ ∈ᶜ Γ′
          c∈⇒x∈∘c∈Γ⇐ c∈
            with destruct-∈ᶜ-++ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ]) c∈
          ... | inj₂ (here () , refl)
          ... | inj₁ (c∈′ , refl)
            with destruct-∈ᶜ-++ Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) c∈′
          ... | inj₂ (c∈Δ , _) = ⊥-elim $ ∉ᶜ-|| (λ where (here ())) Δ c∈Δ
          ... | inj₁ (c∈Γ , refl)
            = begin
              c∈⇒x∈ Γ c∈Γ
            ≡˘⟨ ∈-resp-↭∘∈-ids-++⁺ˡ (c∈⇒x∈ Γ c∈Γ) ⟩
              ( ∈-resp-↭ (↭-reflexive namesʳ≡) -- x ∈ ids Γ
              ∘ ∈-ids-++⁺ˡ (Γ ∣ Γ₁) Γ₂         -- x ∈ ids Γ′
              ∘ ∈-ids-++⁺ˡ Γ Γ₁                -- x ∈ ids (Γ ∣ Γ₁)
              ∘ c∈⇒x∈ Γ                        -- x ∈ ids Γ
              ) c∈Γ                            -- ⟨C,v⟩ₓ ∈ᶜ Γ
            ≡⟨ cong (∈-resp-↭ (↭-reflexive namesʳ≡) ∘ ∈-ids-++⁺ˡ (Γ ∣ Γ₁) Γ₂)
                  $ sym $ c∈⇒x∈∘∈ᶜ-++⁺ˡ {Γ = Γ}{Γ₁} c∈Γ ⟩
              ( ∈-resp-↭ (↭-reflexive namesʳ≡) -- x ∈ ids Γ
              ∘ ∈-ids-++⁺ˡ (Γ ∣ Γ₁) Γ₂         -- x ∈ ids Γ′
              ∘ c∈⇒x∈ (Γ ∣ Γ₁)                 -- x ∈ ids (Γ ∣ Γ₁)
              ∘ ∈ᶜ-++⁺ˡ Γ Γ₁                   -- ⟨C,v⟩ₓ ∈ᶜ (Γ ∣ Γ₁)
              ) c∈Γ                            -- ⟨C,v⟩ₓ ∈ᶜ Γ
            ≡⟨ cong (∈-resp-↭ (↭-reflexive namesʳ≡))
                  $ sym $ c∈⇒x∈∘∈ᶜ-++⁺ˡ {Γ = Γ ∣ Γ₁}{Γ₂} (∈ᶜ-++⁺ˡ Γ Γ₁ c∈Γ) ⟩
              ( ∈-resp-↭ (↭-reflexive namesʳ≡) -- x ∈ ids Γ
              ∘ c∈⇒x∈ Γ′                       -- x ∈ ids Γ′
              ∘ ∈ᶜ-++⁺ˡ (Γ ∣ Γ₁) Γ₂            -- ⟨C,v⟩ₓ ∈ᶜ Γ′
              ∘ ∈ᶜ-++⁺ˡ Γ Γ₁                   -- ⟨C,v⟩ₓ ∈ᶜ (Γ ∣ Γ₁)
              ) c∈Γ                            -- ⟨C,v⟩ₓ ∈ᶜ Γ
            ∎

          ↭-reflexive∘c∈⇒x∈∘c∈Γ⇐ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ′) →
            ( ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
            ∘ c∈⇒x∈ Γ
            ∘ c∈Γ⇐
            ) c∈
            ≡ c∈⇒x∈ Γ′ c∈
          ↭-reflexive∘c∈⇒x∈∘c∈Γ⇐ c∈
            = begin
              ( ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
              ∘ c∈⇒x∈ Γ
              ∘ c∈Γ⇐
              ) c∈
            ≡⟨ cong (∈-resp-↭ (↭-reflexive $ sym namesʳ≡)) (c∈⇒x∈∘c∈Γ⇐ c∈) ⟩
              ( ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
              ∘ ∈-resp-↭ (↭-reflexive namesʳ≡)
              ∘ c∈⇒x∈ Γ′
              ) c∈
            ≡⟨ cong (λ ◆ → ∈-resp-↭ ◆
                         $ ∈-resp-↭ (↭-reflexive namesʳ≡)
                         $ c∈⇒x∈ Γ′ c∈)
                  $ sym $ ↭-sym∘↭-reflexive namesʳ≡ ⟩
              ( ∈-resp-↭ (↭-sym $ ↭-reflexive namesʳ≡)
              ∘ ∈-resp-↭ (↭-reflexive namesʳ≡)
              ∘ c∈⇒x∈ Γ′
              ) c∈
            ≡⟨ Any-resp-↭∘Any-resp-↭˘ (↭-reflexive namesʳ≡) (c∈⇒x∈ Γ′ c∈) ⟩
              c∈⇒x∈ Γ′ c∈
            ∎ where open ≡-Reasoning

          c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
              → R  ≈⋯ ⟨ c , v ⟩at x ⋯
          c∈⇐ = ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
              ∘ c∈Γ⇐
              ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈

          H : (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″)
            → x∈⇒ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡ c∈⇒x∈ (R′ ∙cfg) c∈
          {- i.e. the following diagram commutes

              x ∈                      x ∈
              ids Γ ——————— x∈⇒ —————→ ids (` ad) ++ ids Γ
                ↑                    ⇑
                ∣                    ∥
                ∣                    ∥
              c∈⇒x∈                c∈⇒x∈
                ∣                    ∥
                ∣                    ∥
                Γ ←—————— c∈⇐ —————— Γ′ ≈ ` ad ∣ Γ
          -}
          H c∈ =
            begin
              x∈⇒ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨⟩
              ( x∈⇒
              ∘ c∈⇒x∈ (R ∙cfg)
              ∘ c∈⇐
              ) c∈
            ≡⟨⟩
              ( ∈-resp-↭ namesʳ↭
              ∘ c∈⇒x∈ (R ∙cfg)
              ∘ ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
              ∘ c∈Γ⇐
              ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈
              ) c∈
            ≡⟨⟩
              ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))
              ∘ ∈-resp-↭ (↭-reflexive $ sym namesʳ≡)
              ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
              ∘ c∈⇒x∈ (R ∙cfg)
              ∘ ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
              ∘ c∈Γ⇐
              ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈
              ) c∈
            ≡⟨ cong ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))
                    ∘ ∈-resp-↭ (↭-reflexive $ sym namesʳ≡) )
                  $ ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈˘ Γ (R ∙cfg) (R≈ .proj₂)
                      (c∈Γ⇐ $ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈) ⟩
              ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))
              ∘ ∈-resp-↭ (↭-reflexive $ sym namesʳ≡) ∘ c∈⇒x∈ Γ ∘ c∈Γ⇐
              ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈
              ) c∈
            ≡⟨ cong (∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂)))
                  $ ↭-reflexive∘c∈⇒x∈∘c∈Γ⇐ (∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈) ⟩
              ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈))
              ∘ c∈⇒x∈ Γ′
              ∘ ∈ᶜ-resp-≈ {R′ ∙cfg}{Γ′} Γ≈
              ) c∈
            ≡⟨ ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈ (R′ ∙cfg) Γ′ Γ≈ c∈ ⟩
              c∈⇒x∈ (R′ ∙cfg) c∈
            ∎

          txoutEndC≡ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″) →
            𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC (c∈⇐ c∈)
          txoutEndC≡ c∈ =
            begin
              𝕣′ ∙txoutC c∈
            ≡⟨⟩
              𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
            ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
              𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
              𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨⟩
              𝕣 ∙txoutC (c∈⇐ c∈)
            ∎

      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = $λˢ

      abstract
        value-preserving⇒ :
          ValuePreservingʳᶜ 𝕣
          ────────────────────
          ValuePreservingʳᶜ 𝕣′
        value-preserving⇒ IH c∈ = trans (cong _∙value (txoutEndC≡ _)) (IH (c∈⇐ _))
{-
  -- [3]
  module _ ad Γ₀ A x where
    private
      Γ  = ` ad ∣ Γ₀
      Γ′ = Γ ∣ A auth[ x ▷ˢ ad ]
    module H₃ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        Liftᶜ : nub-participants ad ⊆ committedParticipants ad Γ → 𝔾 ad
        Liftᶜ = LIFT₀ 𝕣 t Γ R≈ ad (here refl)
      private
        names≡ : Γ′ ≡⦅ names ⦆ Γ
        names≡ rewrite collectFromBase-++ {X = Name} Γ (A auth[ x ▷ˢ ad ]) = L.++-identityʳ _

        namesʳ≡ : Γ′ ≡⦅ namesʳ ⦆ Γ
        namesʳ≡ = cong filter₂ names≡

        namesˡ≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
        namesˡ≡ = cong filter₁ names≡

        ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
        ads≡ rewrite collectFromBase-++ {X = Advertisement} Γ (A auth[ x ▷ˢ ad ]) = L.++-identityʳ _

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite namesʳ≡ = txout′

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ rewrite namesˡ≡ = sechash′

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ rewrite collectFromBase-++ {X = Advertisement} Γ (A auth[ x ▷ˢ ad ])
                    | L.++-identityʳ (advertisements Γ)
                    = κ′
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [4]
  module _ ad Γ₀ (ds : List DepositRef) v z where
    private
      g = ad .G
      c = C ad
      partG = g ∙partG
      -- [BUG] cannot get this to work here without explicitly passing ⦃ HPᵖ ⦄
      -- [WORKAROUND1] give it as module parameters (forgetting the fact that it's computed out of `g`
      -- [WORKAROUND2] instantiate and give non-instance version _∙partG

      Γ₁ = ` ad ∣ Γ₀
      Γ₂ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) (ds)
      Γ₃ = || map (_auth[ ♯▷ ad ]) partG
      Γ  = Γ₁ ∣ Γ₂ ∣ Γ₃
      Γ′ = ⟨ c , v ⟩at z ∣ Γ₀
    module H₄ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        committedA : partG ⊆ committedParticipants ad Γ
        committedA {p} p∈ = ∈-collect-++⁺ʳ (Γ₁ ∣ Γ₂) Γ₃ ⦃ ∣committedParticipants∣.go ad ⦄ p∈′
          where p∈′ : p ∈ committedParticipants ad Γ₃
                p∈′ rewrite committedPartG≡ {ad} partG = p∈
      abstract
        Liftᶜ : 𝔾 ad
        Liftᶜ = LIFT₀ 𝕣 t Γ R≈ ad (here refl) committedA

      module H₄′ (tx : TxInput′) where
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
        abstract
          λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
          λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [5]
  module _ c v x Γ₀ A i where
    private
      Γ  = ⟨ c , v ⟩at x ∣ Γ₀
      Γ′ = ⟨ c , v ⟩at x ∣ A auth[ x ▷ (c ‼ i) ] ∣ Γ₀
    module H₅ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        Liftᶜ : ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ] → 𝔾 ad
        Liftᶜ = LIFTᶜ 𝕣

        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id
-}
  -- [6]
  module _ c v y (ds : List (Participant × Value × Id)) Γ₀  c′ y′ where
    private
      vs = proj₁ $ proj₂ $ unzip₃ ds
      xs = proj₂ $ proj₂ $ unzip₃ ds
      Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₀)
      Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀
    module H₆ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        Liftᶜ : ∀ {ad} → ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ] → 𝔾 ad
        Liftᶜ = LIFTᶜ 𝕣
      module H₆′ (tx : TxInput′) where
        private
          open ≡-Reasoning

          namesʳ≡₀ : namesʳ Γ ≡ (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
          namesʳ≡₀ =
            begin
              namesʳ Γ
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (⟨ c , v ⟩at y ∣ Γ₁) Γ₀ ⟩
              (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
            ∎

          namesˡ≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
          namesˡ≡ =
            begin
              namesˡ Γ′
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ (⟨ c′ , v + sum vs ⟩at y′) Γ₀ ⟩
              namesˡ (⟨ c′ , v + sum vs ⟩at y′) ++ namesˡ Γ₀
            ≡⟨⟩
              namesˡ Γ₀
            ≡˘⟨ L.++-identityˡ _ ⟩
              [] ++ namesˡ Γ₀
            ≡˘⟨ cong (_++ namesˡ Γ₀) (go ds) ⟩
              namesˡ (⟨ c′ , v ⟩at y ∣ Γ₁) ++ namesˡ Γ₀
            ≡˘⟨ mapMaybe∘collectFromBase-++ isInj₁ (⟨ c′ , v ⟩at y ∣ Γ₁) Γ₀ ⟩
              namesˡ Γ
            ∎ where
              go : ∀ (ds : List (Participant × Value × Id)) →
                Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
              go [] = refl
              go (_ ∷ []) = refl
              go (_ ∷ xs@(_ ∷ _)) = go xs

          ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
          ads≡ =
            begin
              advertisements Γ′
            ≡⟨⟩
              advertisements Γ₀
            ≡˘⟨ cong (_++ advertisements Γ₀) (go ds) ⟩
              advertisements Γ₁ ++ advertisements Γ₀
            ≡⟨ sym $ collectFromBase-++ Γ₁ Γ₀ ⟩
              advertisements Γ
            ∎ where
              go : ∀ (ds : List (Participant × Value × Id)) →
                Null $ advertisements (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
              go [] = refl
              go (_ ∷ []) = refl
              go (_ ∷ xs@(_ ∷ _)) = go xs

          sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
          sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

          κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
          κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

          -- txoutΓ₀ : Txout Γ₀
          -- txoutΓ₀ = weaken-↦ (txout′ :~ namesʳ≡₀ ⟪ _↦ TxInput′ ⟫) (∈-++⁺ʳ _)

          p⊆ : Γ₀ ⊆⦅ ids ⦆ Γ
          -- p⊆ = ⟪ ids Γ₀ ⊆_ ⟫ namesʳ≡₀ ~: ∈-++⁺ʳ _
          p⊆ = there ∘ ∈-ids-++⁺ʳ Γ₁ Γ₀

          txout↝ : Γ →⦅ Txout ⦆ Γ′
          -- txout↝ txout′ rewrite namesʳ≡₀ = cons-↦ y′ tx $ weaken-↦ txout′ (∈-++⁺ʳ _)
          txout↝ txout′ = cons-↦ y′ tx $ weaken-↦ txout′ p⊆
          -- txout↝ txout′ = cons-↦ y′ tx
          --               $ weaken-↦ (txout′ :~ namesʳ≡₀ ⟪ _↦ TxInput′ ⟫) (∈-++⁺ʳ _)

          Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂

          Γₜ Γₜ′ Γₜ″ : Cfgᵗ
          Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′

          $λˢ : 𝕃 R Γₜ″
          $λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

          𝕒  = $λˢ .proj₁
          R′ = Γₜ″ ∷ R ⊣ 𝕒

          R≈′ : R′ ≈⋯ Γ′ at t′
          R≈′ = refl , Γ≈

          𝕣′ : ℝ R′
          𝕣′ = ℝ-step 𝕣 $λˢ

          cvy  = ⟨ c , v ⟩at y
          cvy′ = ⟨ c , v + sum vs ⟩at y′

          txoutΓ : Txout Γ
          txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

          txoutΓ₀ : Txout Γ₀
          -- txoutΓ₀ = weaken-↦ (txoutΓ :~ namesʳ≡₀ ⟪ _↦ TxInput′ ⟫) (∈-++⁺ʳ _)
          txoutΓ₀ = weaken-↦ txoutΓ p⊆

          txoutΓ′ : Txout Γ′
          -- txoutΓ′ = txout↝ $ Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)
          txoutΓ′ = txout↝ txoutΓ

        {-
          txoutΓ≡ : ∀ {x : Id} (x∈ : x ∈ namesʳ Γ′)
            → (txoutΓ′ x∈ ≡ tx)
            ⊎ (∃ λ (x∈′ : x ∈ namesʳ (R .end)) → txoutΓ′ x∈ ≡ 𝕣 ∙txoutEnd x∈′)
          txoutΓ≡ {x} x∈ with x∈
          ... | here refl  = inj₁ refl
          ... | there x∈Γ₀ = inj₂ (-, eq)
            where
            H : ∀ {A B : Set} {x : A} {xs ys : List A} →
              (eq : xs ≡ ys)
              (f : xs ↦ B)
              (x∈ : x ∈ ys)
              → (f :~ eq ⟪ _↦ B ⟫) x∈
              ≡ f (⟪ x L.Mem.∈_ ⟫ eq ~: x∈)
            H refl _ _ = refl

            eq : txoutΓ′ (there x∈Γ₀)
               ≡ ( 𝕣 ∙txoutEnd_
                 ∘ ∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                 ) (⟪ x L.Mem.∈_ ⟫ namesʳ≡₀ ~: ∈-++⁺ʳ _ x∈Γ₀)
            eq =
              begin
                txoutΓ′ (there x∈Γ₀)
              ≡⟨⟩
                txout↝
                  (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
                  (there x∈Γ₀)
              ≡⟨⟩
                cons-↦ y′ tx
                  (weaken-↦
                     (  (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
                     :~ namesʳ≡₀ ⟪ _↦ TxInput′ ⟫
                     ) (∈-++⁺ʳ _))
                  (there x∈Γ₀)
              ≡⟨⟩
                weaken-↦
                  (  (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
                  :~ namesʳ≡₀ ⟪ _↦ TxInput′ ⟫
                  ) (∈-++⁺ʳ _) x∈Γ₀
              ≡⟨⟩
                (  (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
                :~ namesʳ≡₀ ⟪ _↦ TxInput′ ⟫
                ) (∈-++⁺ʳ _ x∈Γ₀)
              ≡⟨ H namesʳ≡₀ _ _ ⟩
                (Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
                (⟪ x L.Mem.∈_ ⟫ namesʳ≡₀ ~: ∈-++⁺ʳ _ x∈Γ₀)
              ≡⟨⟩
                ( txout′
                ∘ namesʳ⦅end⦆⊆ R
                ∘ ∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                ) (⟪ x L.Mem.∈_ ⟫ namesʳ≡₀ ~: ∈-++⁺ʳ _ x∈Γ₀)
              ≡⟨⟩
                ( 𝕣 ∙txoutEnd_
                ∘ ∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                ) (⟪ x L.Mem.∈_ ⟫ namesʳ≡₀ ~: ∈-++⁺ʳ _ x∈Γ₀)
              ∎

          txoutEnd≡ : ∀ {x : Id} (x∈ : x ∈ namesʳ (R′ .end))
            → (𝕣′ ∙txoutEnd x∈ ≡ tx)
            ⊎ (∃ λ (x∈′ : x ∈ namesʳ (R .end)) → 𝕣′ ∙txoutEnd x∈ ≡ 𝕣 ∙txoutEnd x∈′)
          txoutEnd≡ {x} x∈
            rewrite begin
                𝕣′ ∙txoutEnd x∈
              ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ {x} x∈ ⟩
                txoutΓ′ (∈-resp-↭ (↭-sym $′ ≈⇒namesʳ↭ {Γ′}{Γ″} $′ ↭-sym $ Γ≈) x∈)
              ∎
            = txoutΓ≡ (∈-resp-↭ (↭-sym $′ ≈⇒namesʳ↭ {Γ′}{Γ″} $′ ↭-sym $ Γ≈) x∈)
        -}

{-
          txoutC′ : R′ ≈⋯ cvx ⋯ → TxInput′
          txoutC′ c∈ = txoutΓ′ (c∈⇒x∈ Γ′ $ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈)

            pv-txoutC″ : ValuePreserving {Γ″} txoutC′
            pv-txoutC″ = ValuePreserving⇒ {Γ″}{Γ′} Γ≈ (txoutΓ′ ∘ c∈⇒x∈ Γ′) pv-txoutΓ′

            txoutC≗ : (𝕣′ ∙txoutC_) ≗ txoutC′
            txoutC≗ c∈ =
              begin
                𝕣′ ∙txoutC c∈
              ≡⟨⟩
                𝕣′ ∙txoutEnd (c∈⇒x∈ Γ″ c∈)
              ≡⟨⟩
                𝕣′ ∙txout (namesʳ⦅end⦆⊆ R′ $ c∈⇒x∈ Γ″ c∈)
              ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
                Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ (c∈⇒x∈ Γ″ c∈)
              ≡⟨⟩
                txoutΓ′ (∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {Γ′}{Γ″} $ ↭-sym Γ≈) (c∈⇒x∈ Γ″ c∈))
              ≡⟨ cong txoutΓ′
                 (begin
                   ∈-resp-↭ (↭-sym $ ≈⇒namesʳ↭ {Γ′}{Γ″} $ ↭-sym Γ≈) (c∈⇒x∈ Γ″ c∈)
                 ≡⟨ cong (λ ◆ → ∈-resp-↭ ◆ (c∈⇒x∈ Γ″ c∈))
                    (begin
                      ↭-sym (≈⇒namesʳ↭ {Γ′}{Γ″} $ ↭-sym Γ≈)
                    ≡⟨ ↭-sym∘≈⇒namesʳ↭ {Γ′}{Γ″} $ ↭-sym Γ≈ ⟩
                      ≈⇒namesʳ↭ {Γ″}{Γ′} (↭-sym $ ↭-sym Γ≈)
                    ≡⟨ cong (≈⇒namesʳ↭ {Γ″}{Γ′}) $ L.Perm.↭-sym-involutive Γ≈ ⟩
                      ≈⇒namesʳ↭ {Γ″}{Γ′} Γ≈
                    ∎) ⟩
                   ∈-resp-↭ (≈⇒namesʳ↭ {Γ″}{Γ′} Γ≈) (c∈⇒x∈ Γ″ c∈)
                 ≡⟨ ∈-resp-↭∘c∈⇒x∈ Γ″ Γ′ Γ≈ c∈ ⟩
                   c∈⇒x∈ Γ′ (∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈)
                 ∎) ⟩
                txoutΓ′ (c∈⇒x∈ Γ′ $ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈)
              ≡⟨⟩
                txoutC′ c∈
              ∎

            pv-txoutC′ : ValuePreserving {Γ″} (𝕣′ ∙txoutC_)
            pv-txoutC′ = ValuePreserving≗ {Γ″} _ _ (≗-sym txoutC≗) pv-txoutC″


            txoutC≡ : ∀ (c∈ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯)
              → (𝕣′ ∙txoutC c∈ ≡ tx)
              ⊎ (∃ λ (c∈′ : R ≈⋯ ⟨ c , v ⟩at x ⋯) → 𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC c∈′)
            txoutC≡ c∈
            --   with txoutEnd≡ {x = x} (c∈⇒x∈ (R′ ∙cfg) c∈)
            -- ... | inj₁ eq        = inj₁ eq
            -- ... | inj₂ (x∈ , eq) = inj₂ ({!!} , eq′)
              -- with x∈′ ← ∈-resp-↭ (↭-sym $′ ≈⇒namesʳ↭ {Γ′}{Γ″} $′ ↭-sym $ Γ≈)
              --          $ c∈⇒x∈ (R′ ∙cfg) c∈
              rewrite
                begin
                  𝕣′ ∙txoutC c∈
                ≡⟨⟩
                  𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
                ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _  ⟩
                  ( txoutΓ′
                  ∘ ∈-resp-↭ (↭-sym $′ ≈⇒namesʳ↭ {Γ′}{Γ″} $′ ↭-sym $ Γ≈)
                  ∘ c∈⇒x∈ (R′ ∙cfg)
                  ) c∈
                ∎
              with ∈-resp-↭ (↭-sym $′ ≈⇒namesʳ↭ {Γ′}{Γ″} $′ ↭-sym $ Γ≈) $ c∈⇒x∈ (R′ ∙cfg) c∈
                in x∈≡
            ... | here refl
              = inj₁
              $ begin
                  txoutΓ′ (here refl)
                ≡⟨⟩
                  tx
                ∎
            ... | there x∈′
              = inj₂ $ -,
              (begin
                txoutΓ′ (there x∈′)
              ≡⟨ {!!} ⟩
                𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) c∈R)
              ≡⟨⟩
                𝕣 ∙txoutC c∈R
              ∎)
              where
                c∈Γ₀ : ⟨ c , v ⟩at x ∈ᶜ Γ₀
                c∈Γ₀ = {!!}

                c∈Γ : ⟨ c , v ⟩at x ∈ᶜ Γ
                c∈Γ = ∈ᶜ-++⁺ʳ (⟨ _ , _ ⟩at _ ∣ Γ₁) Γ₀ c∈Γ₀

                c∈R : R ≈⋯ ⟨ c , v ⟩at x ⋯
                c∈R = ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂) c∈Γ

              -- where
              -- eq′ : txoutΓ′ x∈′ ≡ 𝕣 ∙txoutC ?
              -- eq′ =
              --   begin
              --     txoutΓ′ x∈′
              --   -- ≡⟨ eq ⟩
              --   --   𝕣 ∙txoutEnd x∈

        --     c∈Γ⇐ : ⟨ c , v ⟩at x ∈ᶜ Γ′
        --         → (⟨ c , v ⟩at x ≡ ⟨ c′ , v₀ + sum vs ⟩at y′)
        --         ⊎ (⟨ c , v ⟩at x ∈ᶜ Γ)
        --     c∈Γ⇐ = λ where
        --       (here px)  → inj₁ px
        --       (there c∈) → inj₂ $ there $ ∈ᶜ-++⁺ʳ Γ₁ Γ₀ c∈

        --     c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
        --         → x ≢ y′
        --         → R  ≈⋯ ⟨ c , v ⟩at x ⋯
        --     c∈⇐ c∈ x≢ with c∈Γ⇐ $ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈
        --     ... | inj₁ refl = ⊥-elim $ x≢ refl
        --     ... | inj₂ c∈   = ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂) c∈

        --     -- c∈↓ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
        --     --     → x ≡ y′
        --     --     → ⟨ c , v ⟩at x ≡ ⟨ c′ , v₀ + sum vs ⟩at y′
        --     -- c∈↓ c∈ x≡ with c∈Γ⇐ $ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈ c∈
        --     -- ... | inj₁ refl = ⊥-elim $ x≢ refl
        --     -- ... | Inj₂ c∈   = ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂) c∈
-}
        -- abstract
        λˢ : 𝕃 R Γₜ″
        λˢ = $λˢ

        abstract
          value-preserving⇒ʳ :
            ValuePreservingʳ 𝕣
            ───────────────────
            ValuePreservingʳ 𝕣′
          value-preserving⇒ʳ pv-txout = pv-txout′
            where
            pv-txoutΓ : ValuePreserving {Γ} txoutΓ
            pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

            pv-txoutΓ₀ : ValuePreserving {Γ₀} txoutΓ₀
            pv-txoutΓ₀ x∈ =
              begin
                txoutΓ₀ x∈ ∙value
              ≡⟨⟩
                weaken-↦ txoutΓ p⊆ x∈ ∙value
              ≡⟨ pv-weaken-↦ {Γ}{Γ₀} txoutΓ p⊆ pv⊆ pv-txoutΓ x∈ ⟩
                (Γ₀ , x∈) ∙value
              ∎ where open ≡-Reasoning
                      pv⊆ : ValuePreserving⊆ {Γ₀}{Γ} p⊆
                      pv⊆ x∈ =
                        begin
                          (Γ₀ , x∈) ∙value
                        ≡˘⟨ ∈-ids-++⁺ʳ∙value {Γ′ = Γ₀}{Γ₁} x∈ ⟩
                          (Γ₁ ∣ Γ₀ , ∈-ids-++⁺ʳ Γ₁ Γ₀ x∈) ∙value
                        ≡⟨⟩
                          (Γ , there (∈-ids-++⁺ʳ Γ₁ Γ₀ x∈)) ∙value
                        ≡⟨⟩
                          (Γ , p⊆ x∈) ∙value
                        ∎

            postulate val≡ : tx ∙value ≡ v + sum vs

            pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
            pv-txoutΓ′ = pv-cons-↦ val≡ pv-txoutΓ₀

            txoutΓ″ : Txout Γ″
            txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

            pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
            pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

            pv-txout′ : ValuePreservingʳ 𝕣′
            pv-txout′ x∈ =
              begin
                (𝕣′ ∙txoutEnd x∈) ∙value
              ≡⟨ cong _∙value
                    $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
                (txoutΓ″ x∈) ∙value
              ≡⟨ pv-txoutΓ″ _ ⟩
                (Γ″ , x∈) ∙value
              ∎

          value-preserving⇒ :
            ValuePreservingʳᶜ 𝕣
            ────────────────────
            ValuePreservingʳᶜ 𝕣′
          value-preserving⇒ pv-txoutᶜ = pv-txoutRC′
            where
            postulate pv-txout : ValuePreservingʳ 𝕣

            pv-txoutΓ : ValuePreserving {Γ} txoutΓ
            pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

            pv-txoutΓ₀ : ValuePreserving {Γ₀} txoutΓ₀
            pv-txoutΓ₀ x∈ =
              begin
                txoutΓ₀ x∈ ∙value
              ≡⟨⟩
                weaken-↦ txoutΓ p⊆ x∈ ∙value
              ≡⟨ pv-weaken-↦ {Γ}{Γ₀} txoutΓ p⊆ pv⊆ pv-txoutΓ x∈ ⟩
                (Γ₀ , x∈) ∙value
              ∎ where open ≡-Reasoning
                      pv⊆ : ValuePreserving⊆ {Γ₀}{Γ} p⊆
                      pv⊆ x∈ =
                        begin
                          (Γ₀ , x∈) ∙value
                        ≡˘⟨ ∈-ids-++⁺ʳ∙value {Γ′ = Γ₀}{Γ₁} x∈ ⟩
                          (Γ₁ ∣ Γ₀ , ∈-ids-++⁺ʳ Γ₁ Γ₀ x∈) ∙value
                        ≡⟨⟩
                          (Γ , there (∈-ids-++⁺ʳ Γ₁ Γ₀ x∈)) ∙value
                        ≡⟨⟩
                          (Γ , p⊆ x∈) ∙value
                        ∎

            postulate val≡ : tx ∙value ≡ v + sum vs

            pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
            pv-txoutΓ′ = pv-cons-↦ val≡ pv-txoutΓ₀

            txoutΓ″ : Txout Γ″
            txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

            pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
            pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

            𝕣′∙txoutEnd≡ : ∀ (x∈ : x ∈ ids Γ″) → 𝕣′ ∙txoutEnd x∈ ≡ txoutΓ″ x∈
            𝕣′∙txoutEnd≡ x∈ =
              begin
                𝕣′ ∙txoutEnd x∈
              ≡⟨⟩
                𝕣′ ∙txout (namesʳ⦅end⦆⊆ R′ x∈)
              ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
                Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ x∈
              ≡⟨⟩
                txoutΓ″ x∈
              ∎

            pv-txout′ : ValuePreservingʳ 𝕣′
            pv-txout′ x∈ =
              begin
                (𝕣′ ∙txoutEnd x∈) ∙value
              ≡⟨ cong _∙value $ 𝕣′∙txoutEnd≡ x∈ ⟩
                (txoutΓ″ x∈) ∙value
              ≡⟨ pv-txoutΓ″ _ ⟩
                (Γ″ , x∈) ∙value
              ∎

            pv-txoutC′ : ValuePreservingᶜ {𝕣′ ∙cfg} (𝕣′ ∙txoutC_)
            pv-txoutC′ = ValuePreserving⇒ {𝕣′ ∙cfg} (𝕣′ ∙txoutEnd_) pv-txout′

            pv-txoutRC′ : ValuePreservingʳᶜ 𝕣′
            pv-txoutRC′ = pv-txoutC′
          --   with txoutC≡ c∈
          -- ... | inj₁ eq         = trans eq refl
          -- ... | inj₂ (c∈′ , eq) = trans eq (IH c∈′)
            -- = begin
            --   (𝕣′ ∙txoutC c∈) ∙value
            -- ≡⟨⟩
            --   (𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)) ∙value
            -- ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
            --   𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            -- ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
            --   𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            -- ≡⟨⟩
            --   𝕣 ∙txoutC (c∈⇐ c∈)
            -- ≡⟨ {!!} ⟩
            --   v
            -- ∎

{-
  -- [7]
  module _ A a n Γ₀ where
    private
      Γ  = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀
      Γ′ = A ∶ a ♯ n ∣ Γ₀
    module H₇ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [8]
  module _ c v y Γ₀  (vcis : List (Value × Contracts × Id)) where
    private
      Γ  = ⟨ c , v ⟩at y ∣ Γ₀
      xs = proj₂ $ proj₂ $ unzip₃ vcis
      Γ₁ = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis
      Γ′ = Γ₁ ∣ Γ₀
    module H₈ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        Liftᶜ : ∀ {ad} → ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ] → 𝔾 ad
        Liftᶜ = LIFTᶜ 𝕣
      module H₈′ (txout⁺ : xs ↦ TxInput′) where
        private
          hʳ : ∀ (vcis : List (Value × Contracts × Id)) →
            namesʳ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis) ≡ (proj₂ $ proj₂ $ unzip₃ vcis)
          hʳ [] = refl
          hʳ (_ ∷ []) = refl
          hʳ (_ ∷ xs@(_ ∷ _)) = cong (_ ∷_) (hʳ xs)

          hˡ : ∀ (vcis : List (Value × Contracts × Id)) →
            Null $ namesˡ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
          hˡ [] = refl
          hˡ (_ ∷ []) = refl
          hˡ (_ ∷ xs@(_ ∷ _)) = hˡ xs

          hᵃ : ∀ (vcis : List (Value × Contracts × Id)) →
            Null $ advertisements (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
          hᵃ [] = refl
          hᵃ (_ ∷ []) = refl
          hᵃ (_ ∷ xs@(_ ∷ _)) = hᵃ xs
          namesʳ≡₀ : namesʳ Γ ≡ y ∷ namesʳ Γ₀
          namesʳ≡₀ = mapMaybe∘collectFromBase-++ isInj₂ (⟨ c , v ⟩at y) Γ₀

          namesʳ≡ : namesʳ Γ′ ≡ xs ++ namesʳ Γ₀
          namesʳ≡ =
            begin
              namesʳ Γ′
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ₁ Γ₀ ⟩
              namesʳ Γ₁ ++ namesʳ Γ₀
            ≡⟨ cong (_++ namesʳ Γ₀) (hʳ vcis) ⟩
              xs ++ namesʳ Γ₀
            ∎ where open ≡-Reasoning

          namesˡ≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
          namesˡ≡ =
            begin
              namesˡ Γ′
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ Γ₁ Γ₀ ⟩
              namesˡ Γ₁ ++ namesˡ Γ₀
            ≡⟨ cong (_++ namesˡ Γ₀) (hˡ vcis) ⟩
              namesˡ Γ₀
            ≡⟨⟩
              namesˡ Γ
            ∎ where open ≡-Reasoning

          ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
          ads≡ =
            begin
              advertisements Γ′
            ≡⟨ collectFromBase-++ Γ₁ Γ₀ ⟩
              advertisements Γ₁ ++ advertisements Γ₀
            ≡⟨ cong (_++ advertisements Γ₀) (hᵃ vcis) ⟩
              advertisements Γ₀
            ≡⟨⟩
              advertisements Γ
            ∎ where open ≡-Reasoning

          txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝ txout′ rewrite namesʳ≡₀ = extend-↦ (↭-reflexive namesʳ≡) txout⁺ (weaken-↦ txout′ there)

          sechash↝ : Γ →⦅ Sechash ⦆ Γ′
          sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

          κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
          κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
        abstract
          λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
          λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [9]
  module _ c v y Γ₀ A x where
    private
      Γ  = ⟨ c , v ⟩at y ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ Γ₀
    module H₉ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        Liftᶜ : ∀ {ad} → ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ] → 𝔾 ad
        Liftᶜ = LIFTᶜ 𝕣
      module H₉′ (tx : TxInput′) where
        private
          txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝  txout′ = cons-↦ x tx $ weaken-↦ txout′ there
        abstract
          λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
          λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id

  -- [10]
  module _ A v x v′ x′ Γ₀ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
    module H₁₀ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [11]
  module _ A v x v′ x′ y Γ₀ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
      Γ′ = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
    module H₁₁ (R≈ : R ≈⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ (λ x∈ → there (there x∈))

        -- Γ″  = ∃Γ≈ .proj₁
        -- Γₜ″ = Γ″ at t′

        $λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′) -- Γₜ″
        $λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id
      --   𝕒  = $λˢ .proj₁
      --   R′ = Γₜ″ ∷ R ⊣ 𝕒

      --   𝕣′ : ℝ R′
      --   𝕣′ = ℝ-step 𝕣 $λˢ

      -- -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = $λˢ

      -- 𝕣′ : ℝ R′
      -- 𝕣′ = 𝕣′

      -- module _ {c v x} where
      --   private
      --     c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
      --         → R  ≈⋯ ⟨ c , v ⟩at x ⋯
      --     c∈⇐ = ?
        -- abstract
        --   txoutEndC≡ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″) →
        --     𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC (c∈⇐ c∈)
        --   txoutEndC≡ c∈ =
        --     begin
        --       𝕣′ ∙txoutC c∈
        --     ≡⟨⟩
        --       𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
        --     -- ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
        --     --   𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
        --     -- ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
        --     --   𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
        --     ≡⟨ ? ⟩
        --       𝕣 ∙txoutC (c∈⇐ c∈)
        --     ∎ where open ≡-Reasoning

  -- [12]
  module _ A v v′ x Γ₀ where
    private
      Γ  = ⟨ A has (v + v′) ⟩at x ∣ Γ₀
      Γ′ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
    module H₁₂ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [13]
  module _ A v v′ x Γ₀ y y′ where
    private
      Γ  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
    module H₁₃ (R≈ : R ≈⋯ Γ at t) (tx tx′ : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id
          where txout↝ : Γ →⦅ Txout ⦆ Γ′
                txout↝ txout′ = cons-↦ y tx $ cons-↦ y′ tx′ $ weaken-↦ txout′ there

  -- [14]
  module _ A v x Γ₀ B′ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
    module H₁₄ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [15]
  module _ A v x B′ Γ₀ y where
    private
      Γ  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
      Γ′ = ⟨ B′ has v ⟩at y ∣ Γ₀
    module H₁₅ (R≈ : R ≈⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id
          where txout↝ : Γ →⦅ Txout ⦆ Γ′
                txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ there

  -- [16]
  module _ (ds : List (Participant × Value × Id)) Γ₀ (j : Index ds) A y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
      Γ  = Δ ∣ Γ₀
      j′ = Index xs ∋ ‼-map {xs = ds} j
      Γ′ = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
    module H₁₆ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- ** name resolution
      abstract
        xs↦ : xs ↦ TxInput′
        xs↦ = txout′ ∘ xs⊆
          where
          xs⊆ : xs ⊆ namesʳ R
          xs⊆ = begin xs              ⊆⟨ namesʳ-∥map-authDestroy ds ⟩
                      namesʳ Δ        ⊆⟨ mapMaybe-⊆ isInj₂ $ ∈-collect-++⁺ˡ Δ Γ₀ ⟩
                      namesʳ Γ        ⊆⟨ ∈namesʳ-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ R≈) ⟩
                      namesʳ (R .end) ⊆⟨ namesʳ⦅end⦆⊆ R ⟩
                      namesʳ R        ∎ where open ⊆-Reasoning Secret
      --
      private
        names≡ : Γ′ ≡⦅ names ⦆ Γ
        names≡ rewrite collectFromBase-++ {X = Name} (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ]) Γ₀
                    | collectFromBase-++ {X = Name} Δ (A auth[ xs , j′ ▷ᵈˢ y ])
                    | L.++-identityʳ (names Δ)
                    = sym $ collectFromBase-++ {X = Name} Δ Γ₀

        namesʳ≡ :  Γ′ ≡⦅ namesʳ ⦆ Γ
        namesʳ≡ = cong filter₂ names≡

        namesˡ≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
        namesˡ≡ = cong filter₁ names≡

        ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
        ads≡ rewrite collectFromBase-++ {X = Advertisement} (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ]) Γ₀
                  | collectFromBase-++ {X = Advertisement} Δ (A auth[ xs , j′ ▷ᵈˢ y ])
                  | L.++-identityʳ (advertisements Δ)
                  = sym $ collectFromBase-++ {X = Advertisement} Δ Γ₀

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ = lift Γ —⟨ namesʳ ⟩— Γ′ ⊣ namesʳ≡

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝  = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [17]
  module _ (ds : List (Participant × Value × Id)) Γ₀ y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds)
      Γ  = Δ ∣ Γ₀
      Γ′ = Γ₀
    module H₁₇ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- ** name resolution
      abstract
        xs↦ : xs ↦ TxInput′
        xs↦ = txout′ ∘ xs⊆
          where
          xs⊆ : xs ⊆ namesʳ R
          xs⊆ = begin xs              ⊆⟨ namesʳ-∥map-destroy ds ⟩
                      namesʳ Δ        ⊆⟨ mapMaybe-⊆ isInj₂ $ ∈-collect-++⁺ˡ Δ Γ₀ ⟩
                      namesʳ Γ        ⊆⟨ ∈namesʳ-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ R≈) ⟩
                      namesʳ (R .end) ⊆⟨ namesʳ⦅end⦆⊆ R ⟩
                      namesʳ R        ∎ where open ⊆-Reasoning Secret
      --
      private
        namesˡ≡₀ : namesˡ Γ ≡ namesˡ Δ ++ namesˡ Γ₀
        namesˡ≡₀ = mapMaybe∘collectFromBase-++ isInj₁ Δ Γ₀

        namesʳ≡₀ : namesʳ Γ ≡ namesʳ Δ ++ namesʳ Γ₀
        namesʳ≡₀ = mapMaybe∘collectFromBase-++ isInj₂ Δ Γ₀

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite namesʳ≡₀ = weaken-↦ txout′ (∈-++⁺ʳ _)

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ rewrite namesˡ≡₀ = weaken-↦ sechash′ (∈-++⁺ʳ _)

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ = weaken-↦ κ′ (∈-collect-++⁺ʳ Δ Γ₀)
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
-}
  -- [18]
  module _ Γ (R≈ : R ≈⋯ Γ at t) where
    private Γ′ = Γ
    module H₁₈ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        $λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        $λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

        Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ
        Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
        𝕒  = $λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 $λˢ

        namesʳ↭ : R .end ↭⦅ namesʳ ⦆ R′ .end
        namesʳ↭ = ↭-trans (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                          (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))

        txoutΓ : Txout (R .end)
        txoutΓ = 𝕣 ∙txoutEnd_

        txoutΓ′ : Txout Γ′
        txoutΓ′ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)

        x∈⇒ : namesʳ (R .end) ⊆ namesʳ (R′ .end)
        x∈⇒ = ∈-resp-↭ namesʳ↭

        open ≡-Reasoning

        txoutEnd≡ : ∀ {x : Id} (x∈ : x ∈ namesʳ (R .end))
          → 𝕣′ ∙txoutEnd (x∈⇒ x∈) ≡ 𝕣 ∙txoutEnd x∈
        txoutEnd≡ {x} x∈ =
          begin
            𝕣′ ∙txoutEnd (x∈⇒ x∈)
          ≡⟨⟩
            𝕣′ ∙txout (namesʳ⦅end⦆⊆ R′ $ x∈⇒ x∈)
          ≡⟨⟩
            ( txout∷ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′
            ∘ namesʳ⦅end⦆⊆ R′
            ∘ x∈⇒
            ) x∈
          ≡⟨ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ _ txoutΓ′ txout′ _ ⟩
            ( Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ R≈′ .proj₂) txoutΓ′
            ∘ x∈⇒
            ) x∈
          ≡⟨⟩
            ( Txout≈ {Γ′}{Γ″} (↭-sym $ R≈′ .proj₂) txoutΓ′
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym $ R≈′ .proj₂))
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
            ) x∈
          ≡⟨ Txout≗ {Γ′}{Γ″} (↭-sym $ R≈′ .proj₂) txoutΓ′ _ ⟩
            ( Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ
            ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
            ) x∈
          ≡⟨ Txout≗ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ _ ⟩
            txoutΓ x∈
          ≡⟨⟩
            𝕣 ∙txoutEnd x∈
          ∎
{-
        module _ {c v x} where
          c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
              → R  ≈⋯ ⟨ c , v ⟩at x ⋯
          c∈⇐ = ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
              ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈

          txoutEndC≡ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″) →
            𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC (c∈⇐ c∈)
          txoutEndC≡ c∈ =
            begin
              𝕣′ ∙txoutC c∈
            ≡⟨⟩
              𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
            ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
              𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
              𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
            ≡⟨⟩
              𝕣 ∙txoutC (c∈⇐ c∈)
            ∎ where
              H : (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″)
                → x∈⇒ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
                ≡ c∈⇒x∈ (R′ ∙cfg) c∈
              H c∈ =
                begin
                  x∈⇒ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
                ≡⟨⟩
                  ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ″} (↭-sym Γ≈))
                  ∘ ∈-resp-↭ (≈⇒namesʳ↭ {R ∙cfg}{Γ} (R≈ .proj₂))
                  ∘ c∈⇒x∈ (R ∙cfg)
                  ∘ ∈ᶜ-resp-≈ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂)
                  ∘ ∈ᶜ-resp-≈ {Γ″}{Γ′} Γ≈
                  ) c∈
                ≡⟨ cong (∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{Γ″} (↭-sym Γ≈)))
                      (∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈˘ Γ (R ∙cfg) (R≈ .proj₂) _) ⟩
                  ( ∈-resp-↭ (≈⇒namesʳ↭ {Γ′}{R′ ∙cfg} (↭-sym Γ≈))
                  ∘ c∈⇒x∈ Γ′
                  ∘ ∈ᶜ-resp-≈ {R′ ∙cfg}{Γ′} Γ≈
                  ) c∈
                ≡⟨ ∈-resp-↭∘c∈⇒x∈∘∈ᶜ-resp-≈ (R′ ∙cfg) Γ′ Γ≈ c∈ ⟩
                  c∈⇒x∈ (R′ ∙cfg) c∈
                ∎
-}
      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = $λˢ

      abstract
      --   value-preserving⇒ :
      --     ValuePreservingʳᶜ 𝕣
      --     ────────────────────
      --     ValuePreservingʳᶜ 𝕣′
      --   value-preserving⇒ IH c∈ = trans (cong _∙value (txoutEndC≡ _)) (IH (c∈⇐ _))

          value-preserving⇒ʳ :
            ValuePreservingʳ 𝕣
            ───────────────────
            ValuePreservingʳ 𝕣′
          value-preserving⇒ʳ pv-txout x∈ =
            begin
              (𝕣′ ∙txoutEnd x∈) ∙value
            ≡⟨ cong _∙value
                  $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
              (Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ x∈) ∙value
            ≡⟨ ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′
                 (ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout) _ ⟩
              (Γ″ , x∈) ∙value
            ∎
