------------------------------------------------------------------------
-- Symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces
open import Prelude.ToList
open import Prelude.Setoid

module SymbolicModel.Run
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML Participant Honest public
  hiding (∣_∣; `; _∙)

-- Symbolic runs.

Run = Trace _—↠ₜ_

variable R R′ R″ Rˢ Rˢ′ Rˢ″ : Run

infix -1 _——[_]→_
_——[_]→_ : Run → Label → TimedConfiguration → Set
R ——[ α ]→ tc′ = end R —[ α ]→ₜ tc′

_∎⊣_ : (Γₜ : TimedConfiguration) → Initial Γₜ → Run
Γₜ ∎⊣ init  = record {start = Γₜ; end = Γₜ; trace = -, (Γₜ ∎ₜ); init = init}

infixr 2 _⟨_⟩←——_⊣_ _⟨_⟩←——_
_⟨_⟩←——_⊣_ : ∀ Γₜ {x Γₜ′}
  → x —[ α ]→ₜ Γₜ′
  → (R : Run)
  → Γₜ ≈ Γₜ′ × R .end ≈ x
    --———————————————
  → Run
Γₜ ⟨ Γ← ⟩←—— R@(record {trace = _ , Γ↞}) ⊣ eq =
  record R { end = Γₜ; trace = -, (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞) }

_⟨_⟩←——_ : ∀ y {x y′}
  → x —[ α ]→ₜ y′
  → (R : Run)
  → {True $ y ≈? y′}
  → {True $ R .end ≈? x}
    --———————————————
  → Run
(Γₜ ⟨ Γ← ⟩←—— R) {p₁} {p₂} = Γₜ ⟨ Γ← ⟩←—— R ⊣ toWitness p₁ , toWitness p₂

infix 0 _≡⋯_ _≈⋯_ _≈⋯_⋯
_≡⋯_ _≈⋯_ : Run → TimedConfiguration → Set
R ≡⋯ Γ at t = R .end ≡ Γ at t
R ≈⋯ Γ at t = R .end ≈ Γ at t
_≈⋯_⋯ : Run → Cfg → Set
R ≈⋯ Γ ⋯ = Γ ∈ᶜ cfg (R .end)
_≈⋯_⋯_⋯ : Run → Cfg → Cfg → Set
R ≈⋯ Γ ⋯ Γ′ ⋯ = Γ′ ∈ᶜ cfg (R .end) × ∃ _≈⋯ Γ ⋯

𝔸 : Run → Cfgᵗ → Set
𝔸 R Γₜ =
  ∃ λ α → ∃ λ end′ → ∃ λ Γₜ′ →
    Σ (end′ —[ α ]→ₜ Γₜ′) λ Γ← →
      Γₜ ≈ Γₜ′ × R .end ≈ end′

_∷_⊣_ : (Γₜ : Cfgᵗ) (R : Run) → 𝔸 R Γₜ → Run
Γₜ ∷ R ⊣ (α , x , Γₜ′ , Γ← , eq) = _⟨_⟩←——_⊣_ {α} Γₜ {x}{Γₜ′} Γ← R eq

_∷⟩_ : (R : Run) → 𝔸 R Γₜ → Run
_∷⟩_ {Γₜ} = Γₜ ∷_⊣_

allTCfgs⁺ : Run → List⁺ TimedConfiguration
allTCfgs⁺ (record {trace = _ , Γ↠}) = allStatesᵗ⁺ Γ↠

allCfgs⁺ : Run → List⁺ Configuration
allCfgs⁺ = L.NE.map cfg ∘ allTCfgs⁺

allTCfgs : Run → List TimedConfiguration
allTCfgs = toList ∘ allTCfgs⁺

allCfgs : Run → List Configuration
allCfgs = map cfg ∘ allTCfgs

lastCfgᵗ firstCfgᵗ : Run → TimedConfiguration
lastCfgᵗ = L.NE.head ∘ allTCfgs⁺
firstCfgᵗ = L.NE.last ∘ allTCfgs⁺

lastCfg firstCfg : Run → Configuration
lastCfg = cfg ∘ lastCfgᵗ
firstCfg = cfg ∘ firstCfgᵗ

start∈allCfgsᵗ : R .start ∈ allTCfgs⁺ R
start∈allCfgsᵗ {R = record {trace = _ , Γ↞}} with Γ↞
... | _ ∎              = here refl
... | _ —→⟨ _ ⟩ _ ⊢ tr = here refl

end∈allCfgsᵗ : R .end ∈ allTCfgs⁺ R
end∈allCfgsᵗ {R = record {trace = _ , Γ↞}} = go Γ↞
  where
    go : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γₜ′ ∈ allStatesᵗ⁺ tr
    go (_ ∎)              = here refl
    go (_ —→⟨ _ ⟩ _ ⊢ tr) = there (go tr)

infix 0 _⋯∈_ _⋯∈ₜ_
_⋯∈_ : Cfg → Run → Set
Γ ⋯∈ R = Γ ∈ allCfgs R
_⋯∈ₜ_ : Cfgᵗ → Run → Set
Γₜ ⋯∈ₜ R = Γₜ ∈ allTCfgs R

-- Properties.

allTCfgs≡ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → allTCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ allTCfgs R ∷ʳ Γₜ
allTCfgs≡  {α}{Γₜ′}{Γₜ}{R@(record {trace = _ , Γ↞})}{x} Γ← eq =
  begin≡
    allTCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    toList (allTCfgs⁺ $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    toList (allStatesᵗ⁺ $ Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞)
  ≡⟨ cong toList $ allStatesᵗ⁺-∷ʳ Γ↞ Γ← eq ⟩
    toList (allStatesᵗ⁺ Γ↞ ⁺∷ʳ Γₜ)
  ≡⟨⟩
    allTCfgs R ∷ʳ Γₜ
  ∎≡ where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

allCfgs≡ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → allCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ allCfgs R ∷ʳ cfg Γₜ
allCfgs≡  {α}{Γₜ′}{Γₜ}{R@(record {trace = _ , Γ↞})}{x} Γ← eq =
  begin≡
    allCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    map cfg (allTCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (map cfg) (allTCfgs≡ {R = R} Γ← eq) ⟩
    map cfg (allTCfgs R ∷ʳ Γₜ)
  ≡⟨ L.map-++-commute cfg (allTCfgs R) [ Γₜ ] ⟩
    map cfg (allTCfgs R) ++ [ cfg Γₜ ]
  ≡⟨⟩
    allCfgs R ∷ʳ cfg Γₜ
  ∎≡
  where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

ad∈≈⇒ℍ :
    R ≈⋯ Γ at t
  → ` ad ∈ᶜ Γ
    --—————————————————————————————————————
  → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
        (x ⋯∈ R)
      × (y ⋯∈ R)
      × (x ≈ x′ × y ≈ y′)
      × ℍ[C-Advertise]⦅ x′ ↝ y′ ⦆ ad
ad∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) ad∈ =
  advertise⇒∗ tr (traceAdₜ (Initial⇒∉ i) (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) ad∈) tr)

auth-commit∈≈⇒ℍ :
    R ≈⋯ Γ at t
  → A auth[ ♯▷ ad ] ∈ᶜ Γ
    --————————————————————————————————————————————
  → ∃ λ Δ → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
        (x ⋯∈ R)
      × (y ⋯∈ R)
      × (x ≈ x′ × y ≈ y′)
      × ℍ[C-AuthCommit]⦅ x′ ↝ y′ ⦆ ad A Δ
auth-commit∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  let Δ , α∈ = traceAuthCommitₜ (Initial⇒∉ i) (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr
  in  Δ , auth-commit⇒∗ tr α∈

auth-init∈≈⇒ℍ :
    R ≈⋯ Γ at t
  → A auth[ z ▷ˢ ad ] ∈ᶜ Γ
    --————————————————————————————————————————————
  → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
        (x ⋯∈ R)
      × (y ⋯∈ R)
      × (x ≈ x′ × y ≈ y′)
      × ℍ[C-AuthInit]⦅ x′ ↝ y′ ⦆ A ad z
auth-init∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  auth-init⇒∗ tr $ traceAuthInitₜ (Initial⇒∉ i) (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

-- init∈≈⇒ℍ :
--     R ≈⋯ Γ at t
--   → A auth[ z ▷ˢ ad ] ∈ᶜ Γ
--     --————————————————————————————————————————————
--   → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
--         (x ⋯∈ R)
--       × (y ⋯∈ R)
--       × (x ≈ x′ × y ≈ y′)
--       × ℍ[C-Init]⦅ x′ ↝ y′ ⦆ ad
-- init∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
--   init⇒∗ tr $ traceInitₜ (Initial⇒∉ i) (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr
