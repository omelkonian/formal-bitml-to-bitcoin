open import Prelude.Init hiding (T)
open SetAsType
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.Lists.Collections
open import Prelude.Lists.Dec
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Nary
open import Prelude.Traces
open import Prelude.Validity
open import Prelude.Apartness

open import SecureCompilation.ModuleParameters using () renaming (⋯ to $⋯)
module SecureCompilation.Parsing.Dec ($⋯ : $⋯) (let open $⋯ $⋯) where

open import SymbolicModel ⋯′ as S
  hiding ( _∎; begin_
         {-variables-}
         ; Γ₀; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; Δ
         ; R; R′; Rˢ; Rˢ′
         ; A; B; B′
         ; G; C
         ; t; t′; δ; n
         ; ad; g; c; c′; cs; ds; d; vcs
         ; x; x′; y; y′; z; xs
         ; a; as
         ; v; v′; vs
         ; α; p; Σ
         )
open import ComputationalModel ⋯′ finPart keypairs
  hiding ( `; ∣_∣; _`∧_; _`∨_; _`=_; _`<_; `true; ∎
         ; Run; Time; Value; DecEq-Label
         ; HonestMoves; HonestStrategies; ParticipantStrategy
         ; Valid-Strategy; moves
         ; Σ
         ; module AdvM
         {-variables-}
         ; R; R′; R″; Rᶜ
         ; tx; i; t; t′; n; m; m′; λᶜ
         )
  renaming (Label to CLabel; Labels to CLabels)
open import Compiler ⋯′ η
open import Coherence $⋯

-- ** generating fresh variables
open import Prelude.InfEnumerable
postulate instance Enum∞-String : Enumerable∞ String

-- ** collecting advertisement base-configurations
open import Prelude.Coercions
allAds : Cfg → List Ad
allAds = mapMaybe go ∘ to[ Cfg′ ]
  where
    go : BaseCfg → Maybe Ad
    go (`` ad) = just ad
    go _      = nothing

postulate allAds∈ : ∀ {ad Γ} → ad ∈ allAds Γ → ` ad ∈ᶜ Γ

allAdsʳ : Run → List Ad
allAdsʳ R = allAds (R ∙cfg)

module _ {Γₜ Rˢ} {𝕣∗ : ℝ∗ Rˢ} {λˢ Rᶜ λᶜ} where
  getAd₁ : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ → Ad
  getAd₁ (mkℍ {h = h}) = let open H₁-args h in ad

  getAd : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ → Ad
  getAd (mkℍ {h = h}) = let open H₄-args h in ad

  postulate
    getAd∈allAds₁ : ∀ p → getAd₁ p ∈ allAdsʳ Rˢ
    getAd∈allAds  : ∀ p → getAd p ∈ allAdsʳ Rˢ

  getT : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ → ∃Tx
  getT (mkℍ {h = h}) = let open H₄ h in -, -, T

  getM : Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ → Message
  getM (mkℍ {h = h}) =
    let
      open H₁-args h hiding (Rˢ) renaming (ad to ⟨G⟩C)
      txoutΓ = Txout Γ ∋ Txout≈ {Rˢ ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)
      txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
      txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
    in
      encodeAd ⟨G⟩C (txoutG , txoutC)

-- ** constrained versions of inductive case-relations
⦅_⦆_⨾_⨾_~ℍ[1]~_⨾_ : Ad → StepRel
⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ =
  ∃ λ (p : Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ) →
    getAd₁ p ≡ ad
⦅_⦆_⨾_⨾_~ℍ[4]~_⨾_ : Ad → StepRel
⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ =
  ∃ λ (p : Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ) →
    getAd p ≡ ad

-- ** postulated lemmas
⦅ad⦆∈allAds : ∀ {ad Rˢ Rᶜ Γₜ λˢ λᶜ} {𝕣∗ : ℝ∗ Rˢ}
  → ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
  → ad ∈ allAdsʳ Rˢ
⦅ad⦆∈allAds (h , refl) = getAd∈allAds h

postulate
  getM≡ : ∀ {ad Rˢ} {𝕣∗ : ℝ∗ Rˢ} {Rᶜ Γₜ Γₜ′ λˢ λˢ′ A m m′}
    → (p  : ⦅ ad ⦆ Γₜ  ⨾ 𝕣∗ ⨾ λˢ  ~ℍ[1]~ A →∗∶ m ⨾ Rᶜ)
    → (p′ : ⦅ ad ⦆ Γₜ′ ⨾ 𝕣∗ ⨾ λˢ′ ~ℍ[1]~ A →∗∶ m′ ⨾ Rᶜ)
    → m ≡ m′
  getT≡ : ∀ {ad Rˢ} {𝕣∗ : ℝ∗ Rˢ} {Rᶜ Γₜ Γₜ′ λˢ λˢ′ T T′}
    → (p  : ⦅ ad ⦆ Γₜ  ⨾ 𝕣∗ ⨾ λˢ  ~ℍ[4]~ submit T ⨾ Rᶜ)
    → (p′ : ⦅ ad ⦆ Γₜ′ ⨾ 𝕣∗ ⨾ λˢ′ ~ℍ[4]~ submit T′ ⨾ Rᶜ)
    → T ≡ T′
  dec-R≈₄ : ∀ Rˢ ad → Dec $ ∃ λ Γ₀ → ∃ λ t →
    let
      open ∣AD ad
      ds = persistentDeposits G
      vs = map select₂ ds
      xs = map select₃ ds
      v  = sum vs
      Γ₁ = Cfg ∋ ` ad ∣ Γ₀
      Γ₂ = Cfg ∋ || map (λ{ (Aᵢ , vᵢ , xᵢ) →
        ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds
      Γ₃ = Cfg ∋ || map (_auth[ ♯▷ ad ]) partG
    in
      Rˢ ≈⋯ Γ₁ ∣ Γ₂ ∣ Γ₃ at t

-- ** injectivity of constrained case-relations
T≢⇒¬H₁ : ∀ {ad Rˢ} {𝕣∗ : ℝ∗ Rˢ} {Γₜ λˢ Rᶜ A m m′} →
  ∙ ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ A →∗∶ m ⨾ Rᶜ
  ∙ m ≢ m′
    ───────────────────────────────────────────────────────────────
    ¬ (∃ λ Γₜ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ A →∗∶ m′ ⨾ Rᶜ)
T≢⇒¬H₁ h m≢ (_ , _ , h′) = m≢ $ getM≡ h h′

T≢⇒¬H₄ : ∀ {ad Rˢ} {𝕣∗ : ℝ∗ Rˢ} {Γₜ λˢ Rᶜ T T′} →
  ∙ ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ submit T ⨾ Rᶜ
  ∙ T ≢ T′
    ───────────────────────────────────────────────────────────────
    ¬ (∃ λ Γₜ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ submit T′ ⨾ Rᶜ)
T≢⇒¬H₄ h T≢ (_ , _ , h′) = T≢ $ getT≡ h h′

T≢⇒¬H₄′ : ∀ {ad Rˢ} {𝕣∗ : ℝ∗ Rˢ} {Γₜ λˢ Rᶜ ∃T T T′} →
  ∙ ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ submit T ⨾ Rᶜ
  ∙ ∃T ≡ T
  ∙ ∃T ≢ T′
    ───────────────────────────────────────────────────────────────
    ¬ (∃ λ Γₜ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ submit T′ ⨾ Rᶜ)
T≢⇒¬H₄′ h refl = T≢⇒¬H₄ h

module _ (Rˢ : Run) (𝕣∗ : ℝ∗ Rˢ) (Rᶜ : CRun) where

  module _ (A₀ : Participant) (m₀ : Message) (let λᶜ = A₀ →∗∶ m₀) where
    ∀dec-H₁ : ∀ ad → Dec $ ∃ λ Γₜ″ → ∃ λ λˢ →
      ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ
    ∀dec-H₁ ad
      with ¿ Valid ad ¿
         | ¿ Any (_∈ Hon) (ad .Ad.G ∙partG) ¿
         | ¿ ad ⊆⦅ deposits ⦆ (Rˢ ∙cfg) ¿
    ... | _ | _ | no ¬d⊆
      = no λ where
        (_ , _ , mkℍ {h = mk {Γ₀ = Γ₀} _ _ d⊆ (_ ⨾ _ ⨾ _ ⊣ R≈ ≈ _ ⊣ _)} , refl) →
          ¬d⊆ (L.Perm.∈-resp-↭ (≈⇒deposits↭ {Γ₀}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂))  ∘ d⊆)
    ... | no ¬vad | _ | _
      = no λ where (_ , _ , mkℍ {h = mk vad _ _ _} , refl) → ¬vad vad
    ... | _ | no ¬hon | _
      = no λ where (_ , _ , mkℍ {h = mk _ hon _ _} , refl) → ¬hon hon
    ... | yes vad | yes hon | yes d⊆
      = ≫
      where
      t  = Rˢ .end .time
      Γ₀ = Rˢ ∙cfg
      Γ′ = ` ad ∣ Γ₀

      h : H₁-args
      h = mk {Γ₀ = Γ₀} vad hon d⊆ record
        {𝕣∗ = 𝕣∗; Rᶜ = Rᶜ; Γ″ = Γ′; R≈ = refl , ↭-refl; Γ≈ = ↭-refl}

      open H₁-args h using (Γ; 𝕒; R≈; 𝕣; G; C; Γₜ″)
      open H₁ h using (λˢ)
      m =
        let
          txoutΓ = Txout Γ ∋ Txout≈ {Rˢ ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)
          txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {ad}{Γ} d⊆)
          txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
        in
          encodeAd ad (txoutG , txoutC)

      𝕙 : Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[1]~ A₀ →∗∶ m ⨾ Rᶜ
      𝕙 = mkℍ {h}

      𝕙-ad : ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[1]~ A₀ →∗∶ m ⨾ Rᶜ
      𝕙-ad = 𝕙 , refl

      ≫ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ
      ≫ with m ≟ m₀
      ... | no  m≢ = no  $ T≢⇒¬H₁ 𝕙-ad m≢
      ... | yes m≡ = yes $ -, -, QED
        where
        QED : ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[1]~ λᶜ ⨾ Rᶜ
        QED = 𝕙-ad :~ m≡ ⟪ (λ ◆ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[1]~ A₀ →∗∶ ◆ ⨾ Rᶜ) ⟫

    dec-H₁ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ
    dec-H₁ with any? ∀dec-H₁ (allAdsʳ Rˢ)
    ... | yes p∈ =
      let ad , _ , _ , p , _ = L.Any.satisfied p∈
      in yes (-, -, p)
    ... | no  p∉ = no ¬QED
      where
      ¬QED : ¬_ $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ
      ¬QED (_ , _ , p) = p∉ p∈
        where
        ad = getAd₁ p
        ad∈ : ad ∈ allAdsʳ Rˢ
        ad∈ = getAd∈allAds₁ p

        p∈ : Any (λ ad → ∃ λ Γₜ″ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ)
                 (allAdsʳ Rˢ)
        p∈ = L.Any.map (λ where refl → -, -, p , refl) ad∈

    -- similarly for the other cases
    postulate
      dec-H₂ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[2]~ λᶜ ⨾ Rᶜ
      dec-H₃ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[3]~ λᶜ ⨾ Rᶜ
      dec-H₅ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[5]~ λᶜ ⨾ Rᶜ
      dec-H₇ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[7]~ λᶜ ⨾ Rᶜ
      dec-H₁₀ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[10]~ λᶜ ⨾ Rᶜ
      dec-H₁₂ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[12]~ λᶜ ⨾ Rᶜ
      dec-H₁₄ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[14]~ λᶜ ⨾ Rᶜ
      dec-H₁₆ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[16]~ λᶜ ⨾ Rᶜ

      ¬H[1-14] :
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[1]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[2]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[3]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[5]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[7]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[10]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[12]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[14]~ λᶜ ⨾ Rᶜ)
          ────────────────────────────────────────────────────
          ∀ Γₜ″ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ≁₁₁ λᶜ ⨾ Rᶜ

      ¬H16⇒≁₁ :
        ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[16]~ λᶜ ⨾ Rᶜ)
        ────────────────────────────────────────────────────
        ∀ Γₜ″ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ≁₁ λᶜ ⨾ Rᶜ

  module _ (T₀ : ∃Tx) where
    λᶜ = submit T₀

    ∀dec-H₄ : ∀ ad → Dec $ ∃ λ Γₜ″ → ∃ λ λˢ →
      ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
    ∀dec-H₄ ad@(⟨ G ⟩ C)
      with dec-R≈₄ Rˢ ad
    ... | no R≉ = no ¬QED
      where
      ¬QED : ¬_ $ ∃ λ Γₜ″ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
      ¬QED (_ , _ , mkℍ {h} , refl) =
        let open H₄-args h
        in  R≉ (Γ₀ , t , R≈)
    ... | yes (Γ₀ , t , R≈) = ≫
      where
      ds = persistentDeposits G
      vs = map select₂ ds
      xs = map select₃ ds
      v  = sum vs
      ∃fresh-z = fresh ⦃ Enum∞-String ⦄ (xs ++ ids Γ₀)
      z        = ∃fresh-z .proj₁
      fresh-z  : z ∉ xs ++ ids Γ₀
      fresh-z  = ∃fresh-z .proj₂
      Γ′  = Cfg  ∋ ⟨ C , v ⟩at z ∣ Γ₀

      h : H₄-args
      h = mk {Γ₀ = Γ₀} fresh-z record
        {𝕣∗ = 𝕣∗; Rᶜ = Rᶜ; Γ″ = Γ′; R≈ = R≈; Γ≈ = ↭-refl}

      open H₄-args h hiding (𝕣∗; Rᶜ; ad)
      open H₄ h using (λˢ; T)

      𝕙 : Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[4]~ submit (-, -, T) ⨾ Rᶜ
      𝕙 = mkℍ {h}

      abstract
        ∃T : ∃Tx
        ∃T = -, -, T

        ∃T≡ : ∃T ≡ (-, -, T)
        ∃T≡ = refl

      𝕙-ad : ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[4]~ submit (-, -, T) ⨾ Rᶜ
      𝕙-ad = 𝕙 , refl

      ≫ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
      ≫ with T₀ ≟ ∃T
      ... | no T≢
        = no ¬QED
        where
        ¬QED : ¬_ $ ∃ λ Γₜ″ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
        ¬QED = T≢⇒¬H₄′ 𝕙-ad ∃T≡ (≢-sym T≢)
      ... | yes T≡
        = yes $ -, -, QED
        where
        QED : ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[4]~ λᶜ ⨾ Rᶜ
        QED = ⟪ (λ ◆ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[4]~ submit ◆ ⨾ Rᶜ) ⟫
              trans T≡ ∃T≡ ~: 𝕙-ad

    dec-H₄ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
    dec-H₄ with any? ∀dec-H₄ (allAdsʳ Rˢ)
    ... | yes p∈ =
      let ad , _ , _ , p , _ = L.Any.satisfied p∈
      in yes (-, -, p)
    ... | no  p∉ = no ¬QED
      where
      ¬QED : ¬_ $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ
      ¬QED (_ , _ , p) = p∉ p∈
        where
        ad = getAd p
        ad∈ : ad ∈ allAdsʳ Rˢ
        ad∈ = getAd∈allAds p

        p∈ : Any (λ ad → ∃ λ Γₜ″ → ∃ λ λˢ → ⦅ ad ⦆ Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ)
                 (allAdsʳ Rˢ)
        p∈ = L.Any.map (λ where refl → -, -, p , refl) ad∈

    -- similarly for the other cases
    postulate
      dec-H₆ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[6]~ λᶜ ⨾ Rᶜ
      dec-H₈ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[8]~ λᶜ ⨾ Rᶜ
      dec-H₉ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[9]~ λᶜ ⨾ Rᶜ
      dec-H₁₁ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[11]~ λᶜ ⨾ Rᶜ
      dec-H₁₃ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[13]~ λᶜ ⨾ Rᶜ
      dec-H₁₅ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[15]~ λᶜ ⨾ Rᶜ
      dec-H₁₇ : Dec $ ∃ λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[17]~ λᶜ ⨾ Rᶜ

      ¬H[4-15] :
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[4]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[6]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[8]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[9]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[11]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[13]~ λᶜ ⨾ Rᶜ)
        ∙ ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[15]~ λᶜ ⨾ Rᶜ)
          ────────────────────────────────────────────────────
          ∀ Γₜ″ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ≁₁₁ λᶜ ⨾ Rᶜ

      ¬H17⇒♯ : let open ℝ (ℝ∗⇒ℝ 𝕣∗) in
        ¬ ∃ (λ Γₜ″ → ∃ λ λˢ → Γₜ″ ⨾ 𝕣∗ ⨾ λˢ ~ℍ[17]~ λᶜ ⨾ Rᶜ)
        ────────────────────────────────────────────────────
        ∃inputs T₀ ♯ (hashTxⁱ <$> codom txout′)
