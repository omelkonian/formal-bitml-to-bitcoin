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

module SymbolicModel.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest as S
  hiding ( _∎; begin_
         ; {-variables-} g; c; as; vs; xs; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; R′; Δ )
open import SymbolicModel.Collections Participant Honest

-- [BUG] See issue #5464
_≈ᶜ_ = _≈_ ⦃ IS-Cfg ⦄

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

  -- [1]
  module _ Γ (R≈ : R ≈⋯ Γ at t) ad where
    private Γ′ = ` ad ∣ Γ
    module H₁ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id

  -- [2]
  module _ Γ (R≈ : R ≈⋯ Γ at t) B A ad (Δ : List (Secret × Maybe ℕ)) where
    private
      Γ′ = Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ]
      as = proj₁ $ unzip Δ
    module H₂ (sechash⁺ : as ↦ ℤ) (k⃗ : 𝕂²′ ad) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      private
        hʳ : ∀ Δ → Null $ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        hʳ [] = refl
        hʳ (_ ∷ []) = refl
        hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _

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
          ∎ where open ≡-Reasoning

        hᵃ : ∀ Δ → Null $ advertisements (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        hᵃ [] = refl
        hᵃ (_ ∷ []) = refl
        hᵃ (_ ∷ Δ@(_ ∷ _)) rewrite hᵃ Δ = L.++-identityʳ _

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
          ∎ where open ≡-Reasoning

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
          ∎ where open ≡-Reasoning

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
            ... | false | ()--
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

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
      module H₆′ (tx : TxInput′) where -- abstract
        private
          h₁ : ∀ (ds : List (Participant × Value × Id)) →
            Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
          h₁ [] = refl
          h₁ (_ ∷ []) = refl
          h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

          h₁′ : ∀ (ds : List (Participant × Value × Id)) →
            Null $ advertisements (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
          h₁′ [] = refl
          h₁′ (_ ∷ []) = refl
          h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

          namesʳ≡₀ : namesʳ Γ ≡ (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
          namesʳ≡₀ =
            begin
              namesʳ Γ
            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (⟨ c , v ⟩at y ∣ Γ₁) Γ₀ ⟩
              (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
            ∎ where open ≡-Reasoning

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
            ≡˘⟨ cong (_++ namesˡ Γ₀) (h₁ ds) ⟩
              namesˡ (⟨ c′ , v ⟩at y ∣ Γ₁) ++ namesˡ Γ₀
            ≡˘⟨ mapMaybe∘collectFromBase-++ isInj₁ (⟨ c′ , v ⟩at y ∣ Γ₁) Γ₀ ⟩
              namesˡ Γ
            ∎ where open ≡-Reasoning

          ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
          ads≡ =
            begin
              advertisements Γ′
            ≡⟨⟩
              advertisements Γ₀
            ≡˘⟨ cong (_++ advertisements Γ₀) (h₁′ ds) ⟩
              advertisements Γ₁ ++ advertisements Γ₀
            ≡⟨ sym $ collectFromBase-++ Γ₁ Γ₀ ⟩
              advertisements Γ
            ∎ where open ≡-Reasoning

          sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
          sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

          κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
          κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

          txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝ txout′ rewrite namesʳ≡₀ = cons-↦ y′ tx $ weaken-↦ txout′ (∈-++⁺ʳ _)
        abstract
          λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
          λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝

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
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id

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

  -- [18]
  module _ Γ (R≈ : R ≈⋯ Γ at t) where
    private Γ′ = Γ
    module H₁₈ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      abstract
        λˢ : 𝕃 R (∃Γ≈ .proj₁ at t′)
        λˢ = LIFTˢ 𝕣 t α t′ Γ R≈ Γ′ Γ→Γ′ ∃Γ≈ id id id
