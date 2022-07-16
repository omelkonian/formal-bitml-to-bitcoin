open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.Nary using (uncurry₃)
open import Prelude.Ord
open import Prelude.Membership
open import Prelude.General

module SecureCompilation.Args
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel Participant Honest
  hiding (d; ds; c; c′; R; Rˢ; v; y; y′; t; t′; Γ₀; p; vs; xs; as; Δ; Γ; Γ′; Γₜ; Γₜ′; Γₜ″; α)

record CArgs₆ : Set where
  constructor CArgs₆∶
  field
    Rˢ : Run
    𝕣∗ : ℝ∗ Rˢ

  𝕣 = ℝ∗⇒ℝ 𝕣∗
  open ℝ 𝕣
  field
    ds : List (Participant × Value × Id)
    ss : List (Participant × Secret × ℕ)
    c c′ : Contracts
    i : Index c
    v : Value
    y y′ : Id
    Γ₀ : Cfg
    t : Time
    p : Predicate
  open ∣SELECT c i

  -- As , ts = decorations d
  As = decorations d .proj₁
  ts = decorations d .proj₂

  -- (i) xs = x₁⋯xₖ
  -- (_ , vs , xs) = unzip₃ ds
  -- (_ , as , _)  = unzip₃ ss
  vs = unzip₃ ds .proj₂ .proj₁
  xs = unzip₃ ds .proj₂ .proj₂
  as = unzip₃ ss .proj₂ .proj₁
  Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
  Δ   = || map (uncurry₃ _∶_♯_) ss
  Γ₂  = Δ ∣ Γ₀
  Γ₁₂ = Γ₁ ∣ Γ₂
  Γ   = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₂)
  Γₜ  = Γ at t

  -- ii) in Rˢ, α consumes ⟨D+C,v⟩y and the deposits ⟨Aᵢ,vᵢ⟩ₓᵢ to produce ⟨C′,v′⟩y′
  --     where D = ⋯ : put⋯reveal⋯.C′
  --     let t be the maximum deadline in an `after` in front of D
  --     T0D0: what should t′ be in case there are no `after` decorations? (currently any value)
  field
    t≡ : t ≡ maximum t ts
    d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′
    R≈ : Rˢ ≈⋯ Γₜ

  α   = put⦅ xs , as , y ⦆
  Γ′  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
  t′  = t
  Γₜ′ = Γ′ at t′

  field ∃Γ≈ : ∃ (_≈ᶜ Γ′)
  Γₜ″ = ∃Γ≈ .proj₁ at t′

  field
    -- Hypotheses from [C-PutRev]
    fresh-y′ : y′ ∉ y L.∷ ids Γ₁₂
    p⟦Δ⟧≡ : ⟦ p ⟧ Δ ≡ just true
    -- Hypotheses from [Timeout]
    As≡∅ : Null As

  Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
  Γ→Γ′ = [Timeout] As≡∅ ∀≤t put→ refl
    where
      ∀≤t : All (_≤ t′) ts
      ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

      put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
      put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡
           ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

record Args₆ : Set where
  constructor Args₆∶
  field
    R : Run
    𝕣 : ℝ R
    t : Time
    α : Label
    t′ : Time
    c : Contracts
    v : Value
    y : Id
    ds : List (Participant × Value × Id)
    ss : List (Participant × Secret × ℕ)
    Γ₀ : Cfg
    c′ : Contracts
    y′ : Id
    i : Index c
    p : Predicate

  open ℝ 𝕣 public
  open ∣SELECT c i public
  vs = unzip₃ ds .proj₂ .proj₁
  xs = unzip₃ ds .proj₂ .proj₂
  as = unzip₃ ss .proj₂ .proj₁
  Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
  Γ  = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₀)
  Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀

  field
    R≈ : R ≈⋯ Γ at t
    Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′
    ∃Γ≈ : ∃ (_≈ Γ′)
    d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′

CArgs⇒Args₆ : CArgs₆ → Args₆
CArgs⇒Args₆ cargs = record {R = C.Rˢ; Γ₀ = C.Γ₂; C}
  where module C = CArgs₆ cargs
-- CArgs⇒Args₆ cargs = Args₆∶ R t α t′ c v y ds ss Γ₂ c′ y′ i p R≈ Γ→Γ′ ∃Γ≈ d≡
--   where open CArgs₆ cargs renaming (Rˢ to R)
