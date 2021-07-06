open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans)

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

open import Bitcoin.Crypto
open import Bitcoin.Tx

module SymbolicModel.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
  hiding ( _∎; begin_
         ; {-variables-} g; c; as; vs; xs; ad; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; R′; Δ )
open import SymbolicModel.Collections Participant Honest

-- lifting mappings from last configuration to enclosing runs
-- e.g. Γ →⦅ Txout ⟩ Γ′ ———→ R ⇒⟨ Txout ⦆ R′
module Lift (r : ℝ R) t α t′
  Γ (R≈ : R ≈⋯ Γ at t) Γ′
  (valid↝   : Γ at t —[ α ]→ₜ Γ′ at t′)
  (∃Γ≈ : ∃ (_≈ Γ′))
  (txout↝   : Γ →⦅ Txout   ⦆ Γ′)
  (sechash↝ : Γ →⦅ Sechash ⦆ Γ′)
  (κ↝       : Γ →⦅ 𝕂²      ⦆ Γ′)
  where
  open ℝ r

  private
    Γₜ Γₜ′ Γₜ″ : Cfgᵗ

    Γₜ  = Γ at t
    Γₜ′ = Γ′ at t′
    Γ≈  = proj₂ R≈

    Γ″  = proj₁ ∃Γ≈
    Γₜ″ = Γ″ at t′
    Γ′≈ = proj₂ ∃Γ≈

    eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ
    eq = (refl , Γ′≈) , R≈

    R′ = Γₜ″ ⟨ valid↝ ⟩←—— R ⊣ eq

  txout : Txout R′
  txout = Txout≈ {Γ′}{Γ″} (↭-sym Γ′≈)
        $ txout↝
        $ Txout≈ {cfg (R .end)}{Γ} Γ≈ txout′

  sechash : Sechash R′
  sechash = Sechash≈ {Γ′}{Γ″} (↭-sym Γ′≈)
          $ sechash↝
          $ Sechash≈ {cfg (R .end)}{Γ} Γ≈ sechash′

  κ : 𝕂² R′
  κ {ad} ad∈ with ads∈-⊎ {α}{Γₜ′}{Γₜ″}{R}{ad}{Γₜ} valid↝ eq ad∈
  ... | inj₁ ad∈R  = κ′ ad∈R
  ... | inj₂ ad∈Γ″ = κ↝ (𝕂²≈ {cfg (R .end)}{Γ} Γ≈ (weaken-↦ κ′ $ ads⦅end⦆⊆ {R}))
                        (∈ads-resp-≈ ad {Γ″}{Γ′} Γ′≈ ad∈Γ″)

  𝕣′ : ℝ R′
  𝕣′ = [txout: txout ∣sechash: sechash ∣κ: κ ]

  𝕒 : 𝔸 R Γₜ″
  𝕒 = α , Γₜ , Γₜ′ , valid↝ , eq

-- invoking the compiler with the correct mappings, lifting them from the current configuration/run
-- e.g. (Txout R ∣ Γ →⦅ Txout ⦆ G) ———→ Txout G
module Lift₀ (r : ℝ R) (t : Time)
  Γ (R≈ : R ≈⋯ Γ at t) ad
  (txout↝   : Γ →⦅ Txout   ⦆ ad .G)
  (sechash↝ : Γ →⦅ Sechash ⦆ ad .G)
  (ad∈ : ad ∈ advertisements R)
  where
  open ℝ r

  private Γ≈ = proj₂ R≈

  txout₀ : Txout (ad .G)
  txout₀ = txout↝ $ Txout≈ {cfg (R .end)}{Γ} Γ≈ txout′

  sechash₀ : Sechash (ad .G)
  sechash₀ = sechash↝ $ Sechash≈ {cfg (R .end)}{Γ} Γ≈ sechash′

  κ₀ : 𝕂²′ ad
  κ₀ = κ′ ad∈

module _ (𝕣 : ℝ R) (t : Time) (α : Label) (t′ : Time) where
  open ℝ 𝕣

  module _ Γ (cfg≈ : R ≈⋯ Γ at t) ad where
    private
      Γ′ = ` ad ∣ Γ
    module H₁ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public

  module _ Γ (cfg≈ : R ≈⋯ Γ at t) B A ad (Δ : List (Secret × Maybe ℕ)) where
    private
      Γ′ = Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ]
      as = proj₁ $ unzip Δ
    module H₂ (sechash⁺ : proj₁ (unzip Δ) ↦ ℤ) (k⃗ : 𝕂²′ ad) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
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
          ... | false | ()

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝ public

  module _ ad Γ₀ A x where
    private
      g = ad .G
      Γ = ` ad ∣ Γ₀
      Γ′ = Γ ∣ A auth[ x ▷ˢ ad ]
    module H₃ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
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

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝ public

      module H₃′ (ad∈ : ad ∈ authorizedHonAds Γ₀) (names⊆ : g ⊆⦅ names ⦆ Γ₀) where

        txout↝′ : Γ →⦅ Txout ⦆ g
        txout↝′ txout′ = weaken-↦ txout′ (mapMaybe-⊆ isInj₂ names⊆)

        sechash↝′ : Γ →⦅ Sechash ⦆ g
        sechash↝′ sechash′ = weaken-↦ sechash′ (mapMaybe-⊆ isInj₁ names⊆)

        ad∈Γ : ad ∈ advertisements Γ
        ad∈Γ = ad∈

        ad∈′ : ad ∈ advertisements R
        ad∈′ = ads⦅end⦆⊆ {R} $ ∈ads-resp-≈ ad {Γ}{cfg (R .end)} (↭-sym $ proj₂ cfg≈) ad∈Γ

        open Lift₀ 𝕣 t Γ cfg≈ ad txout↝′ sechash↝′ ad∈′ public

  module _ ad Γ₀ (ds : List DepositRef) partG v z where
    private
      g = ad .G
      c = C ad

      -- [BUG] cannot get this to work here without explicitly passing ⦃ HPᵖ ⦄
      -- partG : List Participant
      -- partG = nub-participants g
      -- [WORKAROUND] give it as module parameters (forgetting the fact that it's computed out of `g`

      Γ₁ = ` ad ∣ Γ₀
      Γ₂ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) (ds)
      Γ₃ = || map (_auth[ ♯▷ ad ]) partG
      Γ  = Γ₁ ∣ Γ₂ ∣ Γ₃
      Γ′ = ⟨ c , v ⟩at z ∣ Γ₀

    module H₄ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
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

      ads⊆ : Γ′ ⊆⦅ advertisements ⦆ Γ
      ads⊆ = begin advertisements Γ′ ≡⟨⟩
                   advertisements Γ₀ ⊆⟨ ∈-collect-++⁺ˡ (Γ₁ ∣ Γ₂) Γ₃ ∘ ∈-collect-++⁺ˡ Γ₁ Γ₂ ⟩
                   advertisements Γ  ∎ where open ⊆-Reasoning Advertisement

      module H₄′ (honG : Any (_∈ Hon) partG) (names⊆ : g ⊆⦅ names ⦆ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-collect-++⁺ˡ (Γ₁ ∣ Γ₂) Γ₃ ∘ ∈-collect-++⁺ˡ Γ₁ Γ₂ ∘ ∈-collect-++⁺ʳ (` ad) Γ₀

        txout↝ : Γ →⦅ Txout ⦆ g
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ →⦅ Sechash ⦆ g
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        authH : ∀ {cs : List Cfg}
          → Any (λ c → ad ∈ advertisements c) cs
          → ad ∈ advertisements (|| cs)
        authH {cs = c ∷ []} p with p
        ... | here ad∈ = ad∈
        authH {cs = c ∷ cs@(_ ∷ _)} p with p
        ... | here  ad∈ = ∈-collect-++⁺ˡ c (|| cs) ad∈
        ... | there ad∈ = ∈-collect-++⁺ʳ c (|| cs) (authH ad∈)

        ad∈₀ : ad ∈ advertisements Γ₃
        ad∈₀ = authH h′
          where
            h : ∀ {p} → p ∈ Hon → ad ∈ advertisements (p auth[ ♯▷ ad ])
            h {p} p∈ rewrite dec-true (p ∈? Hon) p∈ = here refl

            h′ : Any (λ ◆ → ad ∈ advertisements ◆) (map (_auth[ ♯▷ ad ]) partG)
            h′ = L.Any.map⁺ {f = _auth[ ♯▷ ad ]} (L.Any.map h honG)

        ad∈ : ad ∈ advertisements Γ
        ad∈ = ∈-collect-++⁺ʳ (Γ₁ ∣ Γ₂) Γ₃ ad∈₀

        ad∈′ : ad ∈ advertisements R
        ad∈′ = ads⦅end⦆⊆ {R} $ ∈ads-resp-≈ ad {Γ}{cfg (R .end)} (↭-sym $ proj₂ cfg≈) ad∈

        open Lift₀ 𝕣 t Γ cfg≈ ad txout↝ sechash↝ ad∈′ public

      module H₄″ (tx : TxInput′) where

        sechash↝′ :  Γ →⦅ Sechash ⦆ Γ′
        sechash↝′ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

        κ↝′ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝′ κ′ = weaken-↦ κ′ ads⊆

        txout↝′ : Γ →⦅ Txout ⦆ Γ′
        txout↝′ txout′ rewrite namesʳ≡₀ = cons-↦ z tx $ weaken-↦ txout′ ∈-++⁺ˡ

        open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝′ sechash↝′ κ↝′ public

  module _ c v x Γ₀ A i where
    private
      Γ  = ⟨ c , v ⟩at x ∣ Γ₀
      Γ′ = ⟨ c , v ⟩at x ∣ A auth[ x ▷ (c ‼ i) ] ∣ Γ₀

    module H₅ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public

      module H₅′ ad (ad∈ : ad ∈ authorizedHonAds R) (names⊆ : ad .G ⊆⦅ names ⦆ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ →⦅ Txout ⦆ ad .G
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ →⦅ Sechash ⦆ ad .G
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≈ ad txout↝ sechash↝ ad∈ public

  module _ c v y (ds : List (Participant × Value × Id)) Γ₀  c′ y′ where
    private
      vs = proj₁ $ proj₂ $ unzip₃ ds
      xs = proj₂ $ proj₂ $ unzip₃ ds
      Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₀)
      Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀
    module H₆ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
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

      module H₆′ (tx : TxInput′) where

        sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
        sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite namesʳ≡₀ = cons-↦ y′ tx $ weaken-↦ txout′ (∈-++⁺ʳ _)

        open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝ public

      module H₆″ ad (ad∈ : ad ∈ authorizedHonAds R) (names⊆ : ad .G ⊆⦅ names ⦆ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-collect-++⁺ʳ (⟨ c , v ⟩at y) (Γ₁ ∣ Γ₀) ∘ ∈-collect-++⁺ʳ Γ₁ Γ₀

        txout↝ : Γ →⦅ Txout ⦆ ad .G
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ →⦅ Sechash ⦆ ad .G
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≈ ad txout↝ sechash↝ ad∈ public

  module _ A a n Γ₀ where
    private
      Γ  = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀
      Γ′ = A ∶ a ♯ n ∣ Γ₀
    module H₇ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public

  module _ c v y Γ₀  (vcis : List (Value × Contracts × Id)) where
    private
      Γ  = ⟨ c , v ⟩at y ∣ Γ₀
      xs = proj₂ $ proj₂ $ unzip₃ vcis
      Γ₁ = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis
      Γ′ = Γ₁ ∣ Γ₀
    module H₈ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
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

      module H₈′ (txout⁺ : xs ↦ TxInput′) where

        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝ txout′ rewrite namesʳ≡₀ = extend-↦ (↭-reflexive namesʳ≡) txout⁺ (weaken-↦ txout′ there)

        sechash↝ : Γ →⦅ Sechash ⦆ Γ′
        sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ namesˡ≡

        κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
        κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

        open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝ public

      module H₈″ ad (ad∈ : ad ∈ authorizedHonAds R) (names⊆ : ad .G ⊆⦅ names ⦆ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ →⦅ Txout ⦆ ad .G
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ →⦅ Sechash ⦆ ad .G
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≈ ad txout↝ sechash↝ ad∈ public

  module _ c v y Γ₀ A x where
    private
      Γ  = ⟨ c , v ⟩at y ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ Γ₀
    module H₉ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where

      module H₉′ (tx : TxInput′) where
        txout↝ : Γ →⦅ Txout ⦆ Γ′
        txout↝  txout′ = cons-↦ x tx $ weaken-↦ txout′ there

        open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id public

      module H₉″ ad (ad∈ : ad ∈ authorizedHonAds R) (names⊆ : ad .G ⊆⦅ names ⦆ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ →⦅ Txout ⦆ ad .G
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ →⦅ Sechash ⦆ ad .G
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≈ ad txout↝ sechash↝ ad∈ public

  module _ A v x v′ x′ Γ₀ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
    module H₁₀ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public

  module _ A v x v′ x′ y Γ₀ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
      Γ′ = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
    module H₁₁ (cfg≈ : R ≈⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      txout↝ : Γ →⦅ Txout ⦆ Γ′
      txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ (λ x∈ → there (there x∈))

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id public

  module _ A v v′ x Γ₀ where
    private
      Γ  = ⟨ A has (v + v′) ⟩at x ∣ Γ₀
      Γ′ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
    module H₁₂ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public

  module _ A v v′ x Γ₀ y y′ where
    private
      Γ  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
    module H₁₃ (cfg≈ : R ≈⋯ Γ at t) (tx tx′ : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      txout↝ : Γ →⦅ Txout ⦆ Γ′
      txout↝ txout′ = cons-↦ y tx $ cons-↦ y′ tx′ $ weaken-↦ txout′ there

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id public

  module _ A v x Γ₀ B′ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
    module H₁₄ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public

  module _ A v x B′ Γ₀ y where
    private
      Γ  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
      Γ′ = ⟨ B′ has v ⟩at y ∣ Γ₀
    module H₁₅ (cfg≈ : R ≈⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      txout↝ : Γ →⦅ Txout ⦆ Γ′
      txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ there

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ id id public

  module _ (ds : List (Participant × Value × Id)) Γ₀ (j : Index ds) A y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = Δ ∣ Γ₀
      j′ = Index xs ∋ ‼-map {xs = ds} j
      Γ′ = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀

    module H₁₆ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where

      -- ** name resolution
      xs⊆ : xs ⊆ namesʳ R
      xs⊆ = ∈namesʳ-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ cfg≈)
          ∘ ⊆-trans (namesʳ-∥map-helper ds) (mapMaybe-⊆ isInj₂ $ ∈-collect-++⁺ˡ Δ Γ₀)

      xs↦ : xs ↦ TxInput′
      xs↦ = txout′ ∘ xs⊆
      --

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

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝ public

  module _ (ds : List (Participant × Value × Id)) Γ₀ y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds)
      Γ  = Δ ∣ Γ₀
      Γ′ = Γ₀
    module H₁₇ (cfg≈ : R ≈⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where

      -- ** name resolution
      xs⊆ : xs ⊆ namesʳ R
      xs⊆ = ∈namesʳ-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ cfg≈)
          ∘ ⊆-trans (namesʳ-∥map-helper′ ds) (mapMaybe-⊆ isInj₂ $ ∈-collect-++⁺ˡ Δ Γ₀)

      xs↦ : xs ↦ TxInput′
      xs↦ = txout′ ∘ xs⊆
      --

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

      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ txout↝ sechash↝ κ↝ public

  module _ Γ (cfg≈ : R ≈⋯ Γ at t) where
    private
      Γ′ = Γ
    module H₁₈ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) (∃Γ≈ : ∃ (_≈ Γ′)) where
      open Lift 𝕣 t α t′ Γ cfg≈ Γ′ Γ→Γ′ ∃Γ≈ id id id public
