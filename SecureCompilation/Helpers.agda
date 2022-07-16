-- {-# OPTIONS --auto-inline #-}
-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding (T)
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
  hiding ({-variables-} i)
-- open import ComputationalModel.Accessors

module SecureCompilation.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄

  (Honest : List⁺ Participant)
  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding ( _∎; begin_
         ; {-variables-} t; t′; α; g; c; c′; ds; x; x′; y; y′; as; vs; xs
         ; Γ₀; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; R; R′; Δ; d; v
         )
open import ComputationalModel Participant Honest finPart keypairs as C
  using (_∙value; K̂)
open import SecureCompilation.Compiler Participant Honest η
  using (∃Tx¹; ∃Txᶜ; bitml-compiler)
open import SecureCompilation.Args Participant Honest
  using (Args₆)

-- Convenient wrapper for calling the BitML compiler.
COMPILE : 𝔾 ad → ∃Tx¹ × (subtermsᵃ′ ad ↦′ ∃Txᶜ ∘ removeTopDecorations)
COMPILE {ad = ad} (vad , txout₀ , sechash₀ , κ₀) =
  let
    K : 𝕂 (ad .G)
    K {p} _ = K̂ p

    T , ∀d = bitml-compiler {ad = ad} vad sechash₀ txout₀ K κ₀
  in
    T , (∀d ∘ h-subᶜ {ds = ad .C})

-- Helpers for coherence, in order not to over-complicate the constructor definitions for `_~₁₁_`.
-- Also we need the complete power of rewrites/with that let-only expressions in constructors do not give us.
-- Last, these also export properties that we prove about coherence (e.g. invariants that are preserved).
-- ∙ each module corresponds to an inductive case for Coherence
-- ∙ for typechecking performance, `abstract` all exported definitions (if possible...)
-- ∙ all definitions should be private, except the following:
--   ∘ λˢ : the next symbolic move, along with updated mappings for the resulting state/configuration
--   ∘ Liftᶜ : provides mappings for invoking the compiler (only needed in some cases)
--   ∘ value-preserving⇒ : proof that each mapping transofrmation preserves value assignments

module H₆ (⋯ : Args₆) where
  open Args₆ ⋯
  private
    ∃T : ∃Tx¹
    ∃T =
      let
        ⟨G⟩C″ , _ , _ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ (here refl)
        ⟨ G ⟩ C″ = ⟨G⟩C″
        d∈ : d ∈ subtermsᵃ′ ⟨G⟩C″
        d∈ = c⊆ (L.Mem.∈-lookup i)
        _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)
      in
        ∀d∗ d∈ :~ d≡ ⟪ ∃Txᶜ ⟫

    tx : TxInput′
    tx = (-, -, ∃T .proj₂) at 0F
  abstract
    T : ∃Tx
    T = -, -, ∃T .proj₂
  private
    postulate val≡ : tx ∙value ≡ v + sum vs

    open ≡-Reasoning

    secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
    secrets≡ =
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
    sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

    p⊆ : Γ₀ ⊆⦅ ids ⦆ Γ
    p⊆ = there ∘ ∈-ids-++⁺ʳ Γ₁ Γ₀

    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ txout′ = cons-↦ y′ tx $ weaken-↦ txout′ p⊆

    Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
    Γₜ Γₜ′ Γₜ″ : Cfgᵗ; Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
  -- abstract
  λˢ : 𝕃 R Γₜ″
  λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
  private
    𝕒  = λˢ .proj₁
    R′ = Γₜ″ ∷ R ⊣ 𝕒

    R≈′ : R′ ≈⋯ Γ′ at t′
    R≈′ = refl , Γ≈

    𝕣′ : ℝ R′
    𝕣′ = ℝ-step 𝕣 λˢ
  abstract
    value-preserving⇒ :
      ValuePreservingʳ 𝕣
      ───────────────────
      ValuePreservingʳ 𝕣′
    value-preserving⇒ pv-txout = pv-txout′
      where
      txoutΓ : Txout Γ
      txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

      pv-txoutΓ : ValuePreserving {Γ} txoutΓ
      pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

      txoutΓ₀ : Txout Γ₀
      txoutΓ₀ = weaken-↦ txoutΓ p⊆

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

      txoutΓ′ : Txout Γ′
      txoutΓ′ = txout↝ txoutΓ

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


module _ {R} (𝕣 : ℝ R) t α t′ where
  open ℝ 𝕣

  -- [1]
  module _ Γ (R≈ : R ≈⋯ Γ at t) ad where
    private Γ′ = ` ad ∣ Γ
    module H₁ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ; Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id
      private
        𝕒  = λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 λˢ

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈
      abstract
        value-preserving⇒ :
          ValuePreservingʳ 𝕣
          ───────────────────
          ValuePreservingʳ 𝕣′
        value-preserving⇒ pv-txout = pv-txout′
          where
          open ≡-Reasoning

          txoutΓ : Txout (R .end)
          txoutΓ = 𝕣 ∙txoutEnd_

          txoutΓ′ : Txout Γ′
          txoutΓ′ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ

          pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
          pv-txoutΓ′ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ pv-txout

          txoutΓ″ : Txout Γ″
          txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

          pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
          pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

          pv-txout′ : ValuePreservingʳ 𝕣′
          pv-txout′ x∈ =
            begin
              (𝕣′ ∙txoutEnd x∈) ∙value
            ≡⟨ cong _∙value $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
              (txoutΓ″ x∈) ∙value
            ≡⟨ pv-txoutΓ″ _ ⟩
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

        ids≡ : Γ′ ≡⦅ namesʳ ⦆ Γ
        ids≡ =
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

        secrets≡ : namesˡ Γ′ ≡ namesˡ Γ ++ as
        secrets≡ =
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
        ads≡ rewrite collectFromBase-++ {X = Advertisement}
                       (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ])
                    | collectFromBase-++ {X = Advertisement}
                        Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
                    | hᵃ Δ
                    | L.++-identityʳ (advertisements Γ)
                    = refl

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        -- txout↝ = lift Γ —⟨ namesʳ ⟩— Γ′ ⊣ ids≡
        txout↝ txoutΓ {x} x∈
          with ∈-ids-++⁻ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ]) x∈
        ... | inj₂ ()
        ... | inj₁ x∈
          with ∈-ids-++⁻ Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) x∈
        ... | inj₂ x∈ = contradict $ x∈ :~ hʳ Δ ⟪ x L.Mem.∈_ ⟫
          where
          hʳ : ∀ Δ → Null $ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
          hʳ [] = refl
          hʳ (_ ∷ []) = refl
          hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _
        ... | inj₁ x∈ = txoutΓ x∈

        sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ = extend-↦ (↭-reflexive secrets≡) sechash′ sechash⁺

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ = extend-↦ (↭-reflexive ads≡) κ′ κ″
          where
            κ″ : advertisements (A auth[ ♯▷ ad ]) ↦′ 𝕂²′
            κ″ x∈ with does (A ∈? Hon) | x∈
            ... | true  | here refl = k⃗
            ... | false | ()

        Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ; Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
      private
        𝕒  = λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 λˢ

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈
      abstract
        value-preserving⇒ :
          ValuePreservingʳ 𝕣
          ───────────────────
          ValuePreservingʳ 𝕣′
        value-preserving⇒ pv-txout = pv-txout′
          where
          open ≡-Reasoning

          txoutR : Txout (R ∙cfg)
          txoutR = 𝕣 ∙txoutEnd_

          txoutΓ : Txout Γ
          txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutR

          pv-txoutΓ : ValuePreserving {Γ} txoutΓ
          pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutR pv-txout

          txoutΓ′ : Txout Γ′
          txoutΓ′ = txout↝ txoutΓ

          pv↝ : ValuePreserving↝ {Γ}{Γ′} txout↝
          pv↝ txoutΓ pv-txoutΓ {x} x∈
            with ∈-ids-++⁻ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ]) x∈
          ... | inj₂ ()
          ... | inj₁ x∈
            with ∈-ids-++⁻ Γ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) x∈
          ... | inj₂ x∈ = contradict $ x∈ :~ hʳ Δ ⟪ x L.Mem.∈_ ⟫
            where
            hʳ : ∀ Δ → Null $ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
            hʳ [] = refl
            hʳ (_ ∷ []) = refl
            hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _
          ... | inj₁ x∈ = pv-txoutΓ x∈

          pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
          pv-txoutΓ′ = pv↝ txoutΓ pv-txoutΓ

          txoutΓ″ : Txout Γ″
          txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

          pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
          pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

          pv-txout′ : ValuePreservingʳ 𝕣′
          pv-txout′ x∈ =
            begin
              (𝕣′ ∙txoutEnd x∈) ∙value
            ≡⟨ cong _∙value $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→Γ′ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
              (txoutΓ″ x∈) ∙value
            ≡⟨ pv-txoutΓ″ _ ⟩
              (Γ″ , x∈) ∙value
            ∎

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

        ids≡ : Γ′ ≡⦅ namesʳ ⦆ Γ
        ids≡ = cong filter₂ names≡

        secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
        secrets≡ = cong filter₁ names≡

        ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
        ads≡ rewrite collectFromBase-++ {X = Advertisement} Γ (A auth[ x ▷ˢ ad ]) = L.++-identityʳ _

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite ids≡ = txout′

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ rewrite secrets≡ = sechash′

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

          ids≡ : namesʳ Γ ≡ namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
          ids≡ =
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

          secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
          secrets≡ = sym $
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
          sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

          κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
          κ↝ κ′ = weaken-↦ κ′ ads⊆′

          txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝ txout′ rewrite ids≡ = cons-↦ z tx $ weaken-↦ txout′ ∈-++⁺ˡ
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
{-
  module _ c v y (ds : List (Participant × Value × Id)) (ss : List (Participant × Secret × ℕ))
           Γ₀  c′ y′  (i : Index c) p where
    private
      vs = proj₁ $ proj₂ $ unzip₃ ds
      xs = proj₂ $ proj₂ $ unzip₃ ds
      as = proj₁ $ proj₂ $ unzip₃ ss
      Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₀)
      Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀
      open ∣SELECT c i
    module H₆ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′))
      (d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′)
      where
      -- abstract
      --   Liftᶜ : ∀ {ad} → ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ] → 𝔾 ad
      --   Liftᶜ = LIFTᶜ 𝕣
      -- module H₆′ (tx : TxInput′) where
    private
      ∃T : ∃Tx¹
      ∃T = let ⟨G⟩C″ , _ , _ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ (here refl)
               ⟨ G ⟩ C″ = ⟨G⟩C″
               d∈ : d ∈ subtermsᵃ′ ⟨G⟩C″
               d∈ = c⊆ (L.Mem.∈-lookup i)
               _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)
           in ∀d∗ d∈ :~ d≡ ⟪ ∃Txᶜ ⟫

      tx : TxInput′
      tx = (-, -, ∃T .proj₂) at 0F
    abstract
      T : ∃Tx
      T = -, -, ∃T .proj₂
    private
      postulate val≡ : tx ∙value ≡ v + sum vs

      open ≡-Reasoning

      secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
      secrets≡ =
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
      sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

      κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
      κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

      p⊆ : Γ₀ ⊆⦅ ids ⦆ Γ
      p⊆ = there ∘ ∈-ids-++⁺ʳ Γ₁ Γ₀

      txout↝ : Γ →⦅ Txout ⦆ Γ′
      txout↝ txout′ = cons-↦ y′ tx $ weaken-↦ txout′ p⊆

      Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
      Γₜ Γₜ′ Γₜ″ : Cfgᵗ; Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
    -- abstract
    λˢ : 𝕃 R Γₜ″
    λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
    private
      𝕒  = λˢ .proj₁
      R′ = Γₜ″ ∷ R ⊣ 𝕒

      R≈′ : R′ ≈⋯ Γ′ at t′
      R≈′ = refl , Γ≈

      𝕣′ : ℝ R′
      𝕣′ = ℝ-step 𝕣 λˢ
    abstract
      value-preserving⇒ :
        ValuePreservingʳ 𝕣
        ───────────────────
        ValuePreservingʳ 𝕣′
      value-preserving⇒ pv-txout = pv-txout′
        where
        txoutΓ : Txout Γ
        txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

        pv-txoutΓ : ValuePreserving {Γ} txoutΓ
        pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

        txoutΓ₀ : Txout Γ₀
        txoutΓ₀ = weaken-↦ txoutΓ p⊆

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

        txoutΓ′ : Txout Γ′
        txoutΓ′ = txout↝ txoutΓ

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

-}
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
          ids≡ : namesʳ Γ ≡ y ∷ namesʳ Γ₀
          ids≡ = mapMaybe∘collectFromBase-++ isInj₂ (⟨ c , v ⟩at y) Γ₀

          ids≡ : namesʳ Γ′ ≡ xs ++ namesʳ Γ₀
          ids≡ =
            begin
              namesʳ Γ′
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ₁ Γ₀ ⟩
              namesʳ Γ₁ ++ namesʳ Γ₀
            ≡⟨ cong (_++ namesʳ Γ₀) (hʳ vcis) ⟩
              xs ++ namesʳ Γ₀
            ∎ where open ≡-Reasoning

          secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
          secrets≡ =
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
          txout↝ txout′ rewrite ids≡ = extend-↦ (↭-reflexive ids≡) txout⁺ (weaken-↦ txout′ there)

          sechash↝ : Γ →⦅ Sechash ⦆ Γ′
          sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

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

      -- -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id

      private
        𝕒  = λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 λˢ

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

        ids≡ :  Γ′ ≡⦅ namesʳ ⦆ Γ
        ids≡ = cong filter₂ names≡

        secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
        secrets≡ = cong filter₁ names≡

        ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
        ads≡ rewrite collectFromBase-++ {X = Advertisement} (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ]) Γ₀
                  | collectFromBase-++ {X = Advertisement} Δ (A auth[ xs , j′ ▷ᵈˢ y ])
                  | L.++-identityʳ (advertisements Δ)
                  = sym $ collectFromBase-++ {X = Advertisement} Δ Γ₀

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ = lift Γ —⟨ namesʳ ⟩— Γ′ ⊣ ids≡

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝  = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
-}

  -- [17]
  module _ (ds : List (Participant × Value × Id)) Γ₀ y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                  (enumerate ds)
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
        secrets≡ : namesˡ Γ ≡ namesˡ Δ ++ namesˡ Γ₀
        secrets≡ = mapMaybe∘collectFromBase-++ isInj₁ Δ Γ₀

        ids≡ : namesʳ Γ ≡ namesʳ Δ ++ namesʳ Γ₀
        ids≡ = mapMaybe∘collectFromBase-++ isInj₂ Δ Γ₀

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite ids≡ = weaken-↦ txout′ (∈-++⁺ʳ _)

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ rewrite secrets≡ = weaken-↦ sechash′ (∈-++⁺ʳ _)

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ = weaken-↦ κ′ (∈-collect-++⁺ʳ Δ Γ₀)

        Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ; Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝
      private
        𝕒  = λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 λˢ
      abstract
        value-preserving⇒ :
          ValuePreservingʳ 𝕣
          ───────────────────
          ValuePreservingʳ 𝕣′
        value-preserving⇒ pv-txout = pv-txout′
          where
            open ≡-Reasoning

            txoutΓ : Txout Γ
            txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

            pv-txoutΓ : ValuePreserving {Γ} txoutΓ
            pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

            postulate pv↝ : ValuePreserving↝ {Γ}{Γ′} txout↝
            -- pv↝ txoutΓ pv-txoutΓ {x} x∈
            --   = ?

            txoutΓ′ : Txout Γ′
            txoutΓ′ = txout↝ txoutΓ

            pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
            pv-txoutΓ′ =  pv↝ txoutΓ pv-txoutΓ

            txoutΓ″ : Txout Γ″
            txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

            pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
            pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

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

  -- [18]
  module _ Γ (R≈ : R ≈⋯ Γ at t) where
    private Γ′ = Γ
    module H₁₈ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        Γ″ = ∃Γ≈ .proj₁; Γ≈ = ∃Γ≈ .proj₂
        Γₜ Γₜ′ Γₜ″ : Cfgᵗ; Γₜ  = Γ at t; Γₜ′ = Γ′ at t′; Γₜ″ = Γ″ at t′
      -- abstract
      λˢ : 𝕃 R Γₜ″
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id
      private
        𝕒  = λˢ .proj₁
        R′ = Γₜ″ ∷ R ⊣ 𝕒

        R≈′ : R′ ≈⋯ Γ′ at t′
        R≈′ = refl , Γ≈

        𝕣′ : ℝ R′
        𝕣′ = ℝ-step 𝕣 λˢ
      abstract
        value-preserving⇒ :
          ValuePreservingʳ 𝕣
          ───────────────────
          ValuePreservingʳ 𝕣′
        value-preserving⇒ pv-txout = pv-txout′
          where
            open ≡-Reasoning

            txoutΓ : Txout Γ
            txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

            pv-txoutΓ : ValuePreserving {Γ} txoutΓ
            pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

            txoutΓ′ : Txout Γ′
            txoutΓ′ = txoutΓ

            pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
            pv-txoutΓ′ = pv-txoutΓ

            txoutΓ″ : Txout Γ″
            txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

            pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
            pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

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
