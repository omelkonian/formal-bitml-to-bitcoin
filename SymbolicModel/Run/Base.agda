open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Traces
open import Prelude.ToList
open import Prelude.Setoid

module SymbolicModel.Run.Base
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML Participant Honest

Run = Trace _—↠ₜ_
variable R R′ R″ Rˢ Rˢ′ Rˢ″ : Run

_∙partG : Precondition → List Participant
_∙partG = nub-participants

_∙trace′ : (R : Run) → R .start —[ R .trace .proj₁ ]↠ₜ R .end
R ∙trace′ = R .trace .proj₂

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

infix 0 _⋯∈_ _⋯∈ᵗ_
_⋯∈_ : Cfg × Cfg → Run → Set
(Γ , Γ′) ⋯∈ R = (Γ , Γ′) ∈ allTransitions (R ∙trace′)
_⋯∈ᵗ_ : Cfgᵗ × Cfgᵗ → Run → Set
(Γₜ , Γₜ′) ⋯∈ᵗ R = (Γₜ , Γₜ′) ∈ allTransitionsᵗ (R ∙trace′)

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
_≡⋯_ _≈⋯_ : Run → Cfgᵗ → Set
R ≡⋯ Γ at t = R .end ≡ Γ at t
R ≈⋯ Γ at t = R .end ≈ Γ at t
_≈⋯_⋯ : Run → Cfg → Set
R ≈⋯ Γ ⋯ = Γ ∈ᶜ R .end .cfg
_≈⋯_⋯_⋯ : Run → Cfg → Cfg → Set
R ≈⋯ Γ ⋯ Γ′ ⋯ = Γ′ ∈ᶜ R .end .cfg × ∃ _≈⋯ Γ ⋯

𝔸 : Run → Cfgᵗ → Set
𝔸 R Γₜ =
  ∃ λ α → ∃ λ end′ → ∃ λ Γₜ′ →
    Σ (end′ —[ α ]→ₜ Γₜ′) λ Γ← →
      Γₜ ≈ Γₜ′ × R .end ≈ end′

_∷_⊣_ : (Γₜ : Cfgᵗ) (R : Run) → 𝔸 R Γₜ → Run
Γₜ ∷ R ⊣ (α , x , Γₜ′ , Γ← , eq) = _⟨_⟩←——_⊣_ {α} Γₜ {x}{Γₜ′} Γ← R eq

splitRunˡ : (R : Run) → (Γₜ , Γₜ′) ⋯∈ᵗ R → Run
splitRunˡ {Γₜ = Γₜ} R xy∈ᵗ =
  let tr′ = splitTraceˡ (R ∙trace′) xy∈ᵗ
  in record R {trace = -, tr′; end = Γₜ}

splitRunˡ-≈⋯ : (R : Run) (xy∈ : (Γₜ , Γₜ′) ⋯∈ᵗ R) → splitRunˡ R xy∈ ≈⋯ Γₜ
splitRunˡ-≈⋯ {Γₜ = Γₜ} _ _ = ≈ᵗ-refl {Γₜ}