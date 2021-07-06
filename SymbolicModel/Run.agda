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

infix 0 _≡⋯_ _≈⋯_
_≡⋯_ _≈⋯_ : Run → TimedConfiguration → Set
R ≡⋯ Γ at t = R .end ≡ Γ at t
R ≈⋯ Γ at t = R .end ≈ Γ at t

𝔸 : Run → Cfgᵗ → Set
𝔸 R Γₜ =
  ∃ λ α → ∃ λ end′ → ∃ λ Γₜ′ →
    Σ (end′ —[ α ]→ₜ Γₜ′) λ Γ← →
      Γₜ ≈ Γₜ′ × R .end ≈ end′

_∷_⊣_ : (Γₜ : Cfgᵗ) (R : Run) → 𝔸 R Γₜ → Run
Γₜ ∷ R ⊣ (α , x , Γₜ′ , Γ← , eq) = _⟨_⟩←——_⊣_ {α} Γₜ {x}{Γₜ′} Γ← R eq

_∷⟩_ : (R : Run) → 𝔸 R Γₜ → Run
_∷⟩_ {Γₜ} = Γₜ ∷_⊣_

≈ᵗ-refl : Γₜ ≈ Γₜ
≈ᵗ-refl = refl , ↭-refl

private
  allStates⁺ : (Γₜ —[ αs ]↠ₜ Γₜ′) → List⁺ TimedConfiguration
  allStates⁺ = λ where
    (tc ∎)              → tc ∷ []
    (tc —→⟨ _ ⟩ _ ⊢ tr) → tc ∷⁺ allStates⁺ tr

  allStates⁺-∷ : ∀ {x′ y y′ z}
    → (Γ→ : x′ —[ α ]→ₜ y′)
    → (eq : Γₜ ≈ x′ × y ≈ y′)
    → (Γ↠ : y —[ αs ]↠ₜ z)
    → allStates⁺ (Γₜ —→ₜ⟨ Γ→ ⟩ eq ⊢ Γ↠) ≡ (Γₜ ∷⁺ allStates⁺ Γ↠)
  allStates⁺-∷ Γ→ eq Γ↠ = refl

  allStates : (Γₜ —[ αs ]↠ₜ Γₜ′) → List TimedConfiguration
  allStates = toList ∘ allStates⁺

  allStates⁺-∷ʳ : ∀ {x y y′}
    → (Γ↞ : x —[ αs ]↠ₜ y)
    → (Γ← : y′ —[ α ]→ₜ Γₜ′)
    → (eq : Γₜ ≈ Γₜ′ × y ≈ y′)
    → allStates⁺ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞) ≡ (allStates⁺ Γ↞ ⁺∷ʳ Γₜ)
  allStates⁺-∷ʳ (_ ∎) _ _ = refl
  allStates⁺-∷ʳ {Γₜ = Γₜ} (x —→⟨ Γ←′ ⟩ eq′ ⊢ Γ↞) Γ← eq =
    begin≡
      allStates⁺ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ x —→ₜ⟨ Γ←′ ⟩ eq′ ⊢ Γ↞)
    ≡⟨⟩
      allStates⁺ (x —→ₜ⟨ Γ←′ ⟩ eq′ ⊢ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞))
    ≡⟨⟩
      x ∷⁺ allStates⁺ (Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞)
    ≡⟨ cong (x ∷⁺_) (allStates⁺-∷ʳ Γ↞ Γ← eq) ⟩
      (x ∷⁺ allStates⁺ Γ↞) ⁺∷ʳ Γₜ
    ≡⟨⟩
      allStates⁺ (x —→ₜ⟨ Γ←′ ⟩ eq′ ⊢ Γ↞) ⁺∷ʳ Γₜ
    ∎≡
    where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

allTCfgs⁺ : Run → List⁺ TimedConfiguration
allTCfgs⁺ (record {trace = _ , Γ↠}) = allStates⁺ Γ↠

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
    go : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γₜ′ ∈ allStates⁺ tr
    go (_ ∎)              = here refl
    go (_ —→⟨ _ ⟩ _ ⊢ tr) = there (go tr)

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
    toList (allStates⁺ $ Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞)
  ≡⟨ cong toList $ allStates⁺-∷ʳ Γ↞ Γ← eq ⟩
    toList (allStates⁺ Γ↞ ⁺∷ʳ Γₜ)
  ≡⟨⟩
    allTCfgs R ∷ʳ Γₜ
  ∎≡
  where
    open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

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

⊆-concatMap⁺ : ∀ {A : Set} {xs : List A} {xss : List (List A)}
  → xs ∈ xss
  → xs ⊆ concat xss
⊆-concatMap⁺ (here refl) = L.Mem.∈-++⁺ˡ
⊆-concatMap⁺ (there xs∈) = L.Mem.∈-++⁺ʳ _ ∘ ⊆-concatMap⁺ xs∈

trace-ad₀ :
    R ≡⋯ (` ad ∣ Γ) at t
    --————————————————————
  → Valid ad
trace-ad₀ {record { trace = _ , tr ; init = init , _ }} refl
  = proj₂ $ hₜ (Initial⇒ad∉ init) tr
