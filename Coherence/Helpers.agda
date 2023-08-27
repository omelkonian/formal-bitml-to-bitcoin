open import Prelude.Init; open SetAsType
open L.Mem
open L.All using (¬Any⇒All¬)
open L.Any using (lookup-index)
open import Prelude.Lists.Mappings
open import Prelude.Lists.Indexed
open import Prelude.Lists.Dec
open import Prelude.Lists.Collections
open import Prelude.Ord
open import Prelude.InferenceRules
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Nary
open import Prelude.Validity
open import Prelude.Traces

open import SecureCompilation.ModuleParameters using (⋯)
module Coherence.Helpers (⋯ : ⋯) (let open ⋯ ⋯) where
open import SymbolicModel ⋯′
  hiding (d)
open import ComputationalModel ⋯′ finPart keypairs
  hiding (R; t; Time; `)
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

-- lifting mappings from the current run to the original advertisement
-- (needed to invoke the compiler)
LIFT₀ : ∀ (r : ℝ R) (t : Time) Γ (R≈ : R ≈⋯ Γ at t) ad →
  ∙ ` ad ∈ᶜ Γ
  ∙ nub-participants ad ⊆ committedParticipants ad Γ
    ─────────────────────────────────────────────────
    𝔾 ad
LIFT₀ {R} r t Γ R≈@(_ , Γ≈) ad ad∈ committedA = vad , txout₀ , sechash₀ , κ₀
  where
  module _
    (let Γᵢ′ , Γᵢ , _ , _ , xy∈ , (x≈ , _) , ℍ = ad∈≈⇒ℍ {R}{Γ} R≈ ad∈)
    (let _ , $vad , honG , _ = ℍ)
    where
    open ℝ r

    vad : Valid ad
    vad = $vad

    txout₀ : Txout (ad .G)
    txout₀ =
      let
        Γᵢ∈ , _ = ∈-allTransitions⁻ (R ∙trace′) xy∈

        txoutΓᵢ : Txout Γᵢ
        txoutΓᵢ = Txout≈ {Γᵢ′}{Γᵢ} x≈
                $ Txout∈ {R = R} txout′ Γᵢ∈
      in
        ℍ[C-Advertise]⇒TxoutG {Γ = Γᵢ}{ad = ad} ℍ txoutΓᵢ

    sechash₀ : Sechash (ad .G)
    sechash₀ = ℍ[C-AuthCommit]∗⇒SechashG {ad = ad}
             $ committed⇒ℍ[C-AuthCommit]∗ {R}{Γ}{t}{ad} R≈ committedA sechash′

    κ₀ : 𝕂²′ ad
    κ₀ =
      let
        ad∈Hon : ad ∈ authorizedHonAds Γ
        ad∈Hon = committed⇒authAd (L.Any.lookup-result honG) {Γ = Γ}
               $ committedA (L.Mem.∈-lookup $ L.Any.index honG)
      in
        weaken-↦ κ′ (ads⦅end⦆⊆ R ∘ ∈ads-resp-≈ _ {Γ}{R ∙cfg} (↭-sym $ R≈ .proj₂))
          $ ∈-collect-++⁺ʳ (` ad) Γ ad∈Hon

LIFTᶜ : ∀ (𝕣 : ℝ Rˢ) {ad c} →
  ∙ ∃[ Rˢ ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
    ─────────────────────────────
    𝔾 ad
LIFTᶜ {R} 𝕣 {ad} ∃H =
  let
    ∃R : ∃[ R ∋ʳ ∃ℍ[C-AuthInit]⦅_↝_⦆⦅ ad ⦆ ]
    ∃R = proj₁ $ ℍ[C-Init]⇒∃ℍ[C-AuthInit] (R .init) (R ∙trace′) $ ∃-weakenP (R ∙trace′) proj₁ ∃H

    x , x′ , _ , _ , xy∈ , (x≈ , _) , _ , _ , _ , _ , Γ≡ , _ , p⊆′ , _  = ∃R

    ad∈ : ` ad ∈ᶜ x
    ad∈ = ∈ᶜ-resp-≈ {x′}{x} (↭-sym x≈)
        $ subst (` ad ∈ᶜ_) (sym Γ≡) (here refl)

    p⊆ : (ad .G ∙partG) ⊆ committedParticipants ad x
    p⊆ = L.Perm.∈-resp-↭ (collectFromList↭ (∣committedParticipants∣.go ad .collect) (↭-sym x≈))
       ∘ p⊆′

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
