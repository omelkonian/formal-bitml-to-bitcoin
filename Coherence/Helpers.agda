open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Lists.Mappings
open import Prelude.Lists.Indexed
open import Prelude.Lists.Dec
open import Prelude.Ord
open import Prelude.Nary
open import Prelude.InferenceRules
open import Prelude.FromN

open import SecureCompilation.ModuleParameters using (⋯)
module Coherence.Helpers (⋯ : ⋯) (let open ⋯ ⋯) where
open import SymbolicModel ⋯′ hiding (d)
open import ComputationalModel ⋯′ finPart keypairs
open import Compiler ⋯′ η

label≢ : ∀ {A m B m′} →
  m ≢ m′
  ──────────────────
  A →∗∶ m ≢ B →∗∶ m′
label≢ m≢ refl = m≢ refl

∣_∣ᵐ : Message → ℕ
∣ m ∣ᵐ = Nat.Bin.size (fromℕ Integer.∣ m ∣)

-- Checking past oracle interactions.
CheckInteractions : List OracleInteraction → Pred₀ (Secret × Maybe ℕ × HashId)
CheckInteractions os = λ where
  (_ , just Nᵢ , hᵢ) →
    ∃ λ B → ∃ λ mᵢ → ((B , mᵢ , hᵢ) ∈ os) × (∣ mᵢ ∣ᵐ ≡ η + Nᵢ)
  (_ , nothing , hᵢ) →
    hᵢ ∉ map select₃ (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ select₂) os)

CheckOracleInteractions : CRun → List (Secret × Maybe ℕ × HashId) → Set
CheckOracleInteractions Rᶜ = All (CheckInteractions $ oracleInteractionsᶜ Rᶜ)

-- Convenient wrappers for calling the BitML compiler.

COMPILE : ∀ {ad} → 𝔾 ad → InitTx (ad .G) × (subterms ad ↦′ BranchTx ∘ _∗)
COMPILE {ad = ad} (vad , txout₀ , sechash₀ , κ₀) =
  let
    K : 𝕂 (ad .G)
    K {p} _ = K̂ p

    T , ∀d = bitml-compiler {ad = ad} vad sechash₀ txout₀ K κ₀
  in
    T , weaken-sub {ad} ∀d

COMPILE-INIT : ∀ {ad} → 𝔾 ad → InitTx (ad .G)
COMPILE-INIT = proj₁ ∘ COMPILE

COMPILE-SUB : ∀ {ad} → 𝔾 ad → subterms ad ↦′ BranchTx ∘ _∗
COMPILE-SUB = proj₂ ∘ COMPILE

COMPILE-ANCESTOR : ∀ {R c v x Γ t} {i : Index c} (open ∣SELECT c i) →
  ∙ R ≈⋯ Γ at t
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
  ∙ ℝ R
    ──────────────────────────────────────────────
    BranchTx (d ∗) × (authDecorations d ↦ KeyPair)
COMPILE-ANCESTOR {R}{c}{v}{x}{Γ}{t}{i} R≈ c∈ 𝕣 =
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
