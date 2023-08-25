open import Prelude.Init; open SetAsType
open L.Mem
open L.All using (¬Any⇒All¬)
open L.Any using (lookup-index)
open import Prelude.Lists.Mappings
open import Prelude.Lists.Indexed
open import Prelude.Lists.Dec
open import Prelude.Ord
open import Prelude.InferenceRules
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Nary

open import SecureCompilation.ModuleParameters using (⋯)
module Coherence.Helpers (⋯ : ⋯) (let open ⋯ ⋯) where
open import SymbolicModel ⋯′
  hiding (d)
open import ComputationalModel ⋯′ finPart keypairs
  hiding (R; t)
open import Compiler ⋯′ η

-- Checking past oracle interactions.
CheckInteractions : List OracleInteraction → Pred₀ (Secret × Maybe ℕ × HashId)
CheckInteractions os = λ where
  (_ , just Nᵢ , hᵢ) →
    ∃ λ B → ∃ λ mᵢ → ((B , mᵢ , hᵢ) ∈ os) × (∣ mᵢ ∣ᵐ ≡ η + Nᵢ)
  (_ , nothing , hᵢ) →
    hᵢ ∉ map select₃ (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ select₂) os)

CheckOracleInteractions : CRun → List (Secret × Maybe ℕ × HashId) → Set
CheckOracleInteractions Rᶜ = All (CheckInteractions $ oracleInteractionsᶜ Rᶜ)

instance
  Dec-CheckOracle : ∀ {os} → CheckInteractions os ⁇¹
  Dec-CheckOracle {os} {x} .dec
    with x
  ... | _ , nothing , hᵢ = hᵢ ∉? map select₃ (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ select₂) os)
  ... | _ , just Nᵢ , hᵢ
    with ¿ Any (λ (_ , m , h) → (h ≡ hᵢ) × (∣ m ∣ᵐ ≡ η + Nᵢ)) os ¿
  ... | no  x∉ = no λ (_ , _ , x∈ , m≡) →
    L.All.lookup (¬Any⇒All¬ os x∉) x∈ (refl , m≡)
  ... | yes x∈
    with L.Any.lookup x∈ | ∈-lookup {xs = os} (L.Any.index x∈) | lookup-index x∈
  ... | A , m , _ | x∈ | refl , q = yes (A , m , x∈ , q)

-- Convenient wrappers for calling the BitML compiler.
COMPILE :
  𝔾 ad
  ───────────────────────────────────────────────
  InitTx (ad .G) × (subterms ad ↦′ BranchTx ∘ _∗)
COMPILE {ad = ad} (vad , txout₀ , sechash₀ , κ₀) =
  let
    K : 𝕂 (ad .G)
    K {p} _ = K̂ p

    T , ∀d = bitml-compiler {ad = ad} vad sechash₀ txout₀ K κ₀
  in
    T , weaken-sub {ad} ∀d

COMPILE-INIT :
  𝔾 ad
  ──────────────
  InitTx (ad .G)
COMPILE-INIT = proj₁ ∘ COMPILE

COMPILE-SUB :
  𝔾 ad
  ────────────────────────────
  subterms ad ↦′ BranchTx ∘ _∗
COMPILE-SUB = proj₂ ∘ COMPILE

COMPILE-ANCESTOR : ∀ {i : Index c} (open ∣SELECT c i) →
  ∙ R ≈⋯ Γ at t
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
  ∙ ℝ R
    ──────────────────────────────────────────────
    BranchTx (d ∗) × (authDecorations d ↦ KeyPair)
COMPILE-ANCESTOR {c}{R}{Γ}{t}{v}{x}{i} R≈ c∈ 𝕣 =
  let
    -- (ii) {G}C is the ancestor of ⟨C, v⟩ₓ in Rˢ
    ⟨G⟩C , vad , ad∈ , c⊆ , anc = ANCESTOR {R = R} {Γ = Γ} R≈ c∈
    open ∣AD ⟨G⟩C; open ∣SELECT c i; open ℝ 𝕣

    d∈ : d ∈ subterms ⟨G⟩C
    d∈ = c⊆ (L.Mem.∈-lookup i)

    A∈ : authDecorations d ⊆ partG
    A∈ = ∈-nub⁺ ∘ subterms-part⊆ᵃ vad d∈ ∘ auth⊆part {d = d}

    _ , ∀d∗ = COMPILE (LIFTᶜ 𝕣 anc)
  in
    ∀d∗ d∈ , κ′ ad∈ d∈ ∘ A∈
