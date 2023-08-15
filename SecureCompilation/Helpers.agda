-- {-# OPTIONS --auto-inline #-}
open import Prelude.Init hiding (T)
open L.Mem using (_∈_; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.Membership hiding (_∈_)
open import Prelude.Membership.Patterns
open import Prelude.Lists
open import Prelude.Lists.Collections
open import Prelude.Lists.Dec
open import Prelude.Null
open import Prelude.Ord
open import Prelude.Setoid
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.Traces
open import Prelude.Nary
open import Prelude.DecEq

open import Bitcoin.Crypto

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Helpers (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
  hiding ( _∎; begin_
         ; {-variables-} t; t′; α; g; c; c′; cs; ds; x; x′; y; y′; as; vs; xs
         ; Γ₀; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; R; R′; Δ; d; v; vcs
         )
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding ( `; ∣_∣; R′; ∎
         ; {-variables-} tx
         )
open import Compiler ⋯′ η
open import Compiler.Subterms ⋯′
open import SecureCompilation.ComputationalContracts ⋯′

postulate
  SIGᵖ : ∀ {A : Set} → ℤ {- public key -} → A → ℤ

  ∣_∣ᶻ : ℤ → ℕ
  ∣_∣ᵐ : Message → ℕ

CheckInteractions : List OracleInteraction → Pred₀ (Secret × Maybe ℕ × ℤ)
CheckInteractions os = λ where
  (_ , just Nᵢ , hᵢ) →
    ∃ λ B → ∃ λ mᵢ → ((B , mᵢ , hᵢ) ∈ os) × (∣ mᵢ ∣ᵐ ≡ η + Nᵢ)
  (_ , nothing , hᵢ) →
    hᵢ ∉ map select₃ (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ select₂) os)

CheckOracleInteractions : CRun → List (Secret × Maybe ℕ × ℤ) → Set
CheckOracleInteractions Rᶜ = All (CheckInteractions $ oracleInteractionsᶜ Rᶜ)

-- Convenient wrapper for calling the BitML compiler.

COMPILE : 𝔾 ad → InitTx (ad .G) × (subterms ad ↦′ BranchTx ∘ _∗)
COMPILE {ad = ad} (vad , txout₀ , sechash₀ , κ₀) =
  let
    K : 𝕂 (ad .G)
    K {p} _ = K̂ p

    T , ∀d = bitml-compiler {ad = ad} vad sechash₀ txout₀ K κ₀
  in
    T , weaken-sub {ad} ∀d -- ∘ h-subᶜ {ds = ad .C})

-- Helpers for coherence, in order not to over-complicate the constructor definitions for `_~₁₁_`.
-- Also we need the complete power of rewrites/with that let-only expressions in constructors do not give us.
-- Last, these also export properties that we prove about coherence (e.g. invariants that are preserved).
-- ∙ each module corresponds to an inductive case for Coherence
-- ∙ for typechecking performance, `abstract` all exported definitions (if possible...)
-- ∙ all definitions should be private, except the following:
--   ∘ λˢ : the next symbolic move, along with updated mappings for the resulting state/configuration
--   ∘ txoutG/txoutΓ/txoutΓ′ : (optional) mappings for relevant subcomponents
--   ∘ T : (optional) compiled transaction needed for computational move λᶜ
--   ∘ pubK : (optional) public key to sign the transaction
--   ∘ value-preserving⇒ : (T0D0) proof that each mapping transformation preserves value assignments
-- NB: the above should be exported in an `abstract` block to aid typechecking

module _ {R} (𝕣 : ℝ R) t α t′ where
  open ℝ 𝕣

  -- [1]
  module _ Γ (R≈ : R ≈⋯ Γ at t) ad where
    private Γ′ = Cfg ∋ ` ad ∣ Γ
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
      Γ′ = Cfg ∋ Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ]
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
        ads≡ rewrite collectFromBase-++ {X = Ad}
                       (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (A auth[ ♯▷ ad ])
                    | collectFromBase-++ {X = Ad}
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
            ... | true  | 𝟘 = k⃗
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

  -- [3]
  module _ ad Γ₀ A x where
    private
      Γ  = Cfg ∋ ` ad ∣ Γ₀
      Γ′ = Cfg ∋ Γ ∣ A auth[ x ▷ˢ ad ]
    module H₃ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′))
              (committedA : nub-participants ad ⊆ committedParticipants ad Γ) where
      private
        𝕘 : 𝔾 ad
        𝕘 = LIFT₀ 𝕣 t Γ R≈ ad 𝟘 committedA
      -- abstract
      T : ∃Tx
      T = -, -, COMPILE 𝕘 .proj₁
      private
        names≡ : Γ′ ≡⦅ names ⦆ Γ
        names≡ rewrite collectFromBase-++ {X = Name} Γ (A auth[ x ▷ˢ ad ]) = L.++-identityʳ _

        ids≡ : Γ′ ≡⦅ namesʳ ⦆ Γ
        ids≡ = cong filter₂ names≡

        secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
        secrets≡ = cong filter₁ names≡

        ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
        ads≡ rewrite collectFromBase-++ {X = Ad} Γ (A auth[ x ▷ˢ ad ]) = L.++-identityʳ _

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite ids≡ = txout′

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ sechash′ rewrite secrets≡ = sechash′

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ rewrite collectFromBase-++ {X = Ad} Γ (A auth[ x ▷ˢ ad ])
                    | L.++-identityʳ (advertisements Γ)
                    = κ′
      -- abstract
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

      Γ₁ = Cfg ∋ ` ad ∣ Γ₀
      Γ₂ = Cfg ∋ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) (ds)
      Γ₃ = Cfg ∋ || map (_auth[ ♯▷ ad ]) partG
      Γ  = Cfg ∋ Γ₁ ∣ Γ₂ ∣ Γ₃
      Γ′ = Cfg ∋ ⟨ c , v ⟩at z ∣ Γ₀
    module H₄ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        committedA : partG ⊆ committedParticipants ad Γ
        committedA {p} p∈ = ∈-collect-++⁺ʳ (Γ₁ ∣ Γ₂) Γ₃ ⦃ ∣committedParticipants∣.go ad ⦄ p∈′
          where p∈′ : p ∈ committedParticipants ad Γ₃
                p∈′ rewrite committedPartG≡ {ad} partG = p∈
      private
        𝕘 : 𝔾 ad
        𝕘 = LIFT₀ 𝕣 t Γ R≈ ad 𝟘 committedA

        $T : ∃Tx
        $T = -, -, COMPILE 𝕘 .proj₁

        tx : TxInput′
        tx = $T at 0F
      -- abstract
      T : ∃Tx
      T = $T
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
                      advertisements Γ  ∎ where open ⊆-Reasoning Ad

        sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
        sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ κ′ = weaken-↦ κ′ ads⊆′

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite ids≡ = cons-↦ z tx $ weaken-↦ txout′ ∈-++⁺ˡ
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [5]
  module _ c v x Γ₀ A (i : Index c) where
    open ∣SELECT c i
    private
      Γ  = Cfg ∋ ⟨ c , v ⟩at x ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
    module H₅ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′))
              (D≡A:D′ : A ∈ authDecorations d) where
      private
        T×pubK : ∃Tx × ℤ
        T×pubK =
          let
            -- (ii) {G}C is the ancestor of ⟨C, v⟩ₓ in Rˢ
            ⟨G⟩C , vad , ad∈ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ 𝟘
            ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG

            d∈ : d ∈ subterms ⟨G⟩C
            d∈ = c⊆ (L.Mem.∈-lookup i)

            A∈ : A ∈ partG
            A∈ = ∈-nub⁺ $ subterms-part⊆ᵃ vad d∈ $ auth⊆part {d = d} D≡A:D′

            _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)
            Tᵈ : BranchTx (d ∗)
            Tᵈ = ∀d∗ d∈
          in (-, -, Tᵈ) , (κ′ ad∈ d∈ {A} A∈ .pub)
      -- abstract
      T : ∃Tx
      T = T×pubK .proj₁

      pubK : ℤ
      pubK = T×pubK .proj₂
      -- abstract
      -- (iv) txout = txout′, sechash = sechash′, κ = κ′
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [6]
  module _ c v y (ds : DepositRefs) (ss : List (Participant × Secret × ℕ))
           Γ₀  c′ y′  (i : Index c) p where
    private
      vs = proj₁ $ proj₂ $ unzip₃ ds
      xs = proj₂ $ proj₂ $ unzip₃ ds
      as = proj₁ $ proj₂ $ unzip₃ ss
      Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = Cfg ∋ ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₀)
      Γ′ = Cfg ∋ ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀
      open ∣SELECT c i
    module H₆ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′))
      (d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′)
      where
      private
        $T : ∃Tx
        $T = let ⟨G⟩C″ , _ , _ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ 𝟘
                 d∈ : d ∈ subterms ⟨G⟩C″
                 d∈ = c⊆ (L.Mem.∈-lookup i)
                 _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)
            in -, -, (∀d∗ d∈ :~ d≡ ⟪ BranchTx ⟫)

        tx : TxInput′
        tx = $T at 0F
      -- abstract
      T : ∃Tx
      T = $T
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
            go : ∀ (ds : DepositRefs) →
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
            go : ∀ (ds : DepositRefs) →
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

        -- (v) extend txout′ with {y′↦(T,0)}, sechash = sechash′, κ = κ′
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

  -- [7]
  module _ A a n Γ₀ where
    private
      Γ  = Cfg ∋ ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀
      Γ′ = Cfg ∋ A ∶ a ♯ n ∣ Γ₀
    module H₇ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id
  module H₇′
    (Δ : List (Secret × Maybe ℕ))
    (h̅ : List HashId)
    {ad} (k⃗ : 𝕂²′ ad)
    {A} (∃α : auth-commit⦅ A , ad , Δ ⦆ ∈ labelsʳ R) where
    private
      txoutᶜ : Txout ad × Txout (ad .C)
      txoutᶜ = auth-commit∈⇒Txout ∃α 𝕣
    abstract
      -- T0D0: should we search for a signature of this message instead?
      C,h̅,k̅ : HashId
      C,h̅,k̅ = encode {A = HashId × HashId × HashId}
                ( encodeAd ad txoutᶜ
                , encode h̅
                , encode (concatMap (map pub ∘ codom) (codom k⃗))
                )

  -- [8]
  module _ c v y Γ₀ (i : Index c) (vcis : VIContracts) where
    open ∣SELECT c i
    private
      Γ = Cfg ∋ ⟨ c , v ⟩at y ∣ Γ₀
      Γ₁ = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis
      Γ′ = Cfg ∋ Γ₁ ∣ Γ₀
      vs  = unzip₃ vcis .proj₁
      cs  = unzip₃ vcis .proj₂ .proj₁
      vcs = zip vs cs
      xs  = unzip₃ vcis .proj₂ .proj₂
    module H₈ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′))
              (d≡ : d ≡⋯∶ split vcs) where
      private
        $T : ∃Tx
        $T =
          let
            -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
            ⟨G⟩C′ , _ , _ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ 𝟘

            d∈ : d ∈ subterms ⟨G⟩C′
            d∈ = c⊆ (L.Mem.∈-lookup i)

            -- (iii) submit transaction T
            --       where ∙ (T′,o) = txout′(y)
            --             ∙ T is the first transaction in Bpar(cs,d,T′,o,partG,t)
            --       i.e. the one corresponding to subterm `d∗ = split (zip vs cs)`
            _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)

            Tᵈ : Tx 1 (length vcs)
            Tᵈ = ∀d∗ d∈ :~ d≡ ⟪ BranchTx ⟫

            open ≡-Reasoning
            vs≡ , cs≡ , xs≡ = length-unzip₃ vcis

            l≡ : length xs ≡ length (zip vs cs)
            l≡ = sym $
              begin length (zip vs cs)    ≡⟨ L.length-zipWith _,_ vs cs ⟩
                    length vs ⊓ length cs ≡⟨ Nat.m≥n⇒m⊓n≡n
                                           $ Nat.≤-reflexive $ trans cs≡ (sym vs≡) ⟩
                    length cs             ≡⟨ cs≡ ⟩
                    length vcis           ≡⟨ sym xs≡ ⟩
                    length xs             ∎

            Tᵈ′ : Tx 1 (length xs)
            Tᵈ′ = ⟪ Tx 1 ⟫ l≡ ~: Tᵈ
          in
            -, -, Tᵈ′

        -- (iv) extend txout′ with {xᵢ ↦ (T,i)}, sechash = sechash′, κ = κ′
        txout⁺ : xs ↦ TxInput′
        txout⁺ x∈ = $T at L.Any.index x∈
      -- abstract
      T : ∃Tx
      T = $T
      private
        hʳ : ∀ (vcis : VIContracts) →
            namesʳ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
          ≡ (proj₂ $ proj₂ $ unzip₃ vcis)
        hʳ [] = refl
        hʳ (_ ∷ []) = refl
        hʳ (_ ∷ xs@(_ ∷ _)) = cong (_ ∷_) (hʳ xs)

        hˡ : ∀ (vcis : VIContracts) →
          Null $ namesˡ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
        hˡ [] = refl
        hˡ (_ ∷ []) = refl
        hˡ (_ ∷ xs@(_ ∷ _)) = hˡ xs

        hᵃ : ∀ (vcis : VIContracts) →
          Null $ advertisements (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
        hᵃ [] = refl
        hᵃ (_ ∷ []) = refl
        hᵃ (_ ∷ xs@(_ ∷ _)) = hᵃ xs

        ids≡ : namesʳ Γ ≡ y ∷ namesʳ Γ₀
        ids≡ = mapMaybe∘collectFromBase-++ isInj₂ (⟨ c , v ⟩at y) Γ₀

        ids≡′ : namesʳ Γ′ ≡ xs ++ namesʳ Γ₀
        ids≡′ =
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
        txout↝ txout′ rewrite ids≡ = extend-↦ (↭-reflexive ids≡′) txout⁺ (weaken-↦ txout′ there)

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [9]
  module _ c v y Γ₀ A x (i : Index c) where
    open ∣SELECT c i
    private
      Γ  = Cfg ∋ ⟨ c , v ⟩at y ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ A has v ⟩at x ∣ Γ₀
    module H₉ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′))
              (d≡ : d ≡⋯∶ withdraw A) where
      -- abstract
      T : ∃Tx
      T =
          let
            -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
            ⟨G⟩C′ , _ , _ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ 𝟘

            d∈ : d ∈ subterms ⟨G⟩C′
            d∈ = c⊆ (L.Mem.∈-lookup i)

            --   ∙ T′ at o = txout′(x)
            --   ∙ T is the first transaction of Bd(d,d,T′,o,v,partG,0)
            -- i.e.
            -- (iii) submit transaction T
            --       where ∙ (T′,o) = txout′(y)
            --             ∙ T is the first transaction in Bd(d,d,T′,o,v,partG,0)
            --       i.e. the one corresponding to subterm `d∗ = withdraw A`
            _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)
            Tᵈ = ∀d∗ d∈ :~ d≡ ⟪ BranchTx ⟫
          in
            -, -, Tᵈ
      private
        -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝  txout′ = cons-↦ x (T at 0F) $ weaken-↦ txout′ there
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id

  -- [10]
  module _ A v x v′ x′ Γ₀ where
    private
      Γ  = Cfg ∋ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
    module H₁₀ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [11]
  module _ A v x v′ x′ y Γ₀ where
    private
      Γ  = Cfg
         ∋ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ A has (v + v′) ⟩at y ∣ Γ₀
    module H₁₁ (R≈ : R ≈⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ (λ x∈ → there (there x∈))

        -- Γ″  = ∃Γ≈ .proj₁
        -- Γₜ″ = Γ″ at t′

      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′) -- Γₜ″
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id

      -- private
      --   𝕒  = λˢ .proj₁
      --   R′ = Γₜ″ ∷ R ⊣ 𝕒

      --   𝕣′ : ℝ R′
      --   𝕣′ = ℝ-step 𝕣 λˢ

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
      Γ  = Cfg ∋ ⟨ A has (v + v′) ⟩at x ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
    module H₁₂ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [13]
  module _ A v v′ x Γ₀ y y′ where
    private
      Γ  = Cfg ∋ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
    module H₁₃ (R≈ : R ≈⋯ Γ at t) (tx tx′ : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id
        where txout↝ : Γ →⦅ Txout ⦆ Γ′
              txout↝ txout′ = cons-↦ y tx $ cons-↦ y′ tx′ $ weaken-↦ txout′ there

  -- [14]
  module _ A v x Γ₀ B′ where
    private
      Γ  = Cfg ∋ ⟨ A has v ⟩at x ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
    module H₁₄ (R≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [15]
  module _ A v x B′ Γ₀ y where
    private
      Γ  = Cfg ∋ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
      Γ′ = Cfg ∋ ⟨ B′ has v ⟩at y ∣ Γ₀
    module H₁₅ (R≈ : R ≈⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id
        where txout↝ : Γ →⦅ Txout ⦆ Γ′
              txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ there

  -- [16]
  module _ (ds : DepositRefs) Γ₀ (j : Index ds) A y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
      Γ  = Cfg ∋ Δ ∣ Γ₀
      j′ = Index xs ∋ ‼-map {xs = ds} j
      Γ′ = Cfg ∋ Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
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
        ads≡ rewrite collectFromBase-++ {X = Ad} (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ]) Γ₀
                  | collectFromBase-++ {X = Ad} Δ (A auth[ xs , j′ ▷ᵈˢ y ])
                  | L.++-identityʳ (advertisements Δ)
                  = sym $ collectFromBase-++ {X = Ad} Δ Γ₀

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ = lift Γ —⟨ namesʳ ⟩— Γ′ ⊣ ids≡

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝  = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
      -- abstract
      λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
      λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

  -- [17]
  module _ (ds : DepositRefs) Γ₀ y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                  (enumerate ds)
      Γ  = Cfg ∋ Δ ∣ Γ₀
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
