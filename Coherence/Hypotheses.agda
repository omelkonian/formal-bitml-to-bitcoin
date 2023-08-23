open import Prelude.Init hiding (T); open SetAsType
open L.Mem
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Membership.Patterns
open import Prelude.Lists
open import Prelude.Lists.Collections
open import Prelude.Lists.Dec
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Traces
open import Prelude.Null
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Num

open import SecureCompilation.ModuleParameters using (⋯)
module Coherence.Hypotheses (⋯ : ⋯) (let open ⋯ ⋯) where

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
open import SecureCompilation.ComputationalContracts ⋯′
open import Coherence.Helpers ⋯

-- shorthands
SRun : Type
SRun = ∃ ℝ∗

StepRel : Type₁
StepRel = (Γₜ : Cfgᵗ) {Rˢ : S.Run}
        → ℝ∗ Rˢ
        → 𝕃 Rˢ Γₜ
        → CLabel
        → CRun
        → Type

record Transition : Type where
  constructor _⨾_——_—→_⨾_⊣_
  field
    Γ  : Cfg
    t  : Time
    α  : Label
    Γ′ : Cfg
    t′ : Time
  Γₜ  = Cfgᵗ ∋ Γ at t
  Γₜ′ = Cfgᵗ ∋ Γ′ at t′
  field
    Γ→ : Γₜ —[ α ]→ₜ Γₜ′

record ℍ-Run {Γₜ α Γₜ′} (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) : Type where
  constructor _⨾_⨾_⊣_≈_⊣_
  private Γ′ = Γₜ′ .cfg; t′ = Γₜ′ .time
  field
    Rᶜ : CRun
    Rˢ : Run
    𝕣∗ : ℝ∗ Rˢ
    R≈ : Rˢ ≈⋯ Γₜ
    Γ″ : Cfg
    Γ≈ : Γ″ ≈ᶜ Γ′
  Γₜ″ = Cfgᵗ ∋ Γ″ at t′
  ∃Γ≈ = ∃ (_≈ᶜ Γ′) ∋ Γ″ , Γ≈
  𝕣   = ℝ∗⇒ℝ 𝕣∗
  open ℝ 𝕣 public
  𝕒 : 𝔸 Rˢ Γₜ″
  𝕒 = α , Γₜ , Γₜ′ , Γ→ , (refl , Γ≈) , R≈

  Rˢ′ : Run
  Rˢ′ = Γₜ″ ∷ Rˢ ⊣ 𝕒

  R≈′ : Rˢ′ ≈⋯ Γ′ at t′
  R≈′ = refl , Γ≈

  R = Rˢ; R′ = Rˢ′

-- ** Stipulation: advertisting a contract
record H₁-args : Type where
  constructor mk
  field
    {ad Γ₀ t} : _
  open ∣AD ad public
  field
    -- Hypotheses from [C-Advertise]
    vad : ValidAd ad
    hon : Any (_∈ Hon) partG
    d⊆  : ad ⊆⦅ deposits ⦆ Γ₀
  open Transition
    ( Γ₀ ⨾ t —— advertise⦅ ad ⦆ —→ ` ad ∣ Γ₀ ⨾ t
    ⊣ Act ([C-Advertise] vad hon d⊆)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁ (⋯ : H₁-args) (let open H₁-args ⋯) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id
  private
    𝕣′ : ℝ R′
    𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)
  abstract
    value-preserving⇒ :
      ValuePreservingʳ 𝕣
      ───────────────────
      ValuePreservingʳ 𝕣′
    value-preserving⇒ pv-txout = pv-txout′
      where
      open ≡-Reasoning

      txoutΓ : Txout (R .end)
      txoutΓ = 𝕣 ∙txoutEnd_

      txoutΓ′ : Txout Γ′
      txoutΓ′ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ

      pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
      pv-txoutΓ′ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutΓ pv-txout

      txoutΓ″ : Txout Γ″
      txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

      pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
      pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

      pv-txout′ : ValuePreservingʳ 𝕣′
      pv-txout′ x∈ =
        begin
          (𝕣′ ∙txoutEnd x∈) ∙value
        ≡⟨ cong _∙value $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
          (txoutΓ″ x∈) ∙value
        ≡⟨ pv-txoutΓ″ _ ⟩
          (Γ″ , x∈) ∙value
        ∎

data _⨾_⨾_~ℍ[1]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁-args} {A}
    → let
        -- (i) consume {G}C and its persistent deposits from Rˢ
        open H₁-args h renaming (ad to ⟨G⟩C)

        -- txout′ = txout, sechash′ = sechash, κ′ = κ
        open H₁ h using (λˢ)

        m =
          let
            txoutΓ = Txout Γ ∋ Txout≈ {Rˢ ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)
            txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
            txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
          in
            encodeAd ⟨G⟩C (txoutG , txoutC)
        λᶜ = A →∗∶ m
      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[1]~ λᶜ ⨾ Rᶜ

-- ** Stipulation: committing secrets
record H₂-args : Type where
  constructor mk
  field
    {ad Γ₀ t A} : _
    k⃗   : 𝕂²′ ad
    Δ×h̅ : List (Secret × Maybe ℕ × ℤ)
  open ∣AD ad public
    hiding (C)
  h̅  = List HashId             ∋ map (proj₂ ∘ proj₂) Δ×h̅
  Δ  = List (Secret × Maybe ℕ) ∋ map drop₃   Δ×h̅
  Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ
  as = unzip Δ .proj₁
  ms = unzip Δ .proj₂
  k̅  = concatMap (map pub ∘ codom) $ codom k⃗

  sechash⁺ : as ↦ HashId
  sechash⁺ a∈ =
    let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
        (_ , _ , z) , _ = ∈-map⁻ drop₃ a×m∈
    in z
  field
    -- Hypotheses from [C-AuthCommit]
    as≡ : as ≡ secretsOfᵖ A G
    All∉ : All (_∉ secretsOfᶜᶠ A Γ₀) as
    Hon⇒ : A ∈ Hon → All Is-just ms
  open Transition
    ( (` ad ∣ Γ₀) ⨾ t
    —— auth-commit⦅ A , ad , Δ ⦆ —→
      (` ad ∣ Γ₀ ∣ Δᶜ ∣ A auth[ ♯▷ ad ]) ⨾ t
    ⊣ Act ([C-AuthCommit] as≡ All∉ Hon⇒)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₂ (⋯ : H₂-args) (let open H₂-args ⋯) where
  private
    open ≡-Reasoning

    mkRev : List (Secret × Maybe ℕ) → Cfg
    mkRev = ||_ ∘ map (uncurry ⟨ A ∶_♯_⟩)

    ids≡ : Γ′ ≡⦅ ids ⦆ Γ
    ids≡ =
      begin
        ids Γ′
      ≡⟨⟩
        ids (Γ ∣ mkRev Δ ∣ A auth[ ♯▷ ad ])
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (Γ ∣ mkRev Δ) (A auth[ ♯▷ ad ]) ⟩
        ids (Γ ∣ mkRev Δ) ++ ids (A auth[ ♯▷ ad ])
      ≡⟨⟩
        ids (Γ ∣ mkRev Δ) ++ []
      ≡⟨ L.++-identityʳ _ ⟩
        ids (Γ ∣ mkRev Δ)
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ (mkRev Δ) ⟩
        ids Γ ++ ids (mkRev Δ)
      ≡⟨ cong (ids Γ ++_) (hʳ Δ) ⟩
        ids Γ ++ []
      ≡⟨ L.++-identityʳ _ ⟩
        ids Γ
      ∎ where
        hʳ : ∀ Δ → Null $ ids (mkRev Δ)
        hʳ [] = refl
        hʳ (_ ∷ []) = refl
        hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _

    secrets≡ : secrets Γ′ ≡ secrets Γ ++ as
    secrets≡ =
      begin
        secrets Γ′
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ (Γ ∣ mkRev Δ) (A auth[ ♯▷ ad ]) ⟩
        secrets (Γ ∣ mkRev Δ) ++ []
      ≡⟨ L.++-identityʳ _ ⟩
        secrets (Γ ∣ mkRev Δ)
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ Γ (mkRev Δ) ⟩
        secrets Γ ++ secrets (mkRev Δ)
      ≡⟨ cong (secrets Γ ++_) (hˡ Δ) ⟩
        secrets Γ ++ as
      ∎ where
        hˡ : ∀ Δ → secrets (mkRev Δ) ≡ proj₁ (unzip Δ)
        hˡ [] = refl
        hˡ (_ ∷ []) = refl
        hˡ ((s , m) ∷ Δ@(_ ∷ _)) =
          begin
            secrets (⟨ A ∶ s ♯ m ⟩ ∣ mkRev Δ)
          ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ ⟨ A ∶ s ♯ m ⟩ (mkRev Δ) ⟩
            secrets ⟨ A ∶ s ♯ m ⟩ ++ secrets (mkRev Δ)
          ≡⟨⟩
            s ∷ secrets (mkRev Δ)
          ≡⟨ cong (s ∷_) (hˡ Δ) ⟩
            s ∷ proj₁ (unzip Δ)
          ∎

    hᵃ : ∀ Δ → Null $ advertisements (mkRev Δ)
    hᵃ [] = refl
    hᵃ (_ ∷ []) = refl
    hᵃ (_ ∷ Δ@(_ ∷ _)) rewrite hᵃ Δ = L.++-identityʳ _

    ads≡ : advertisements Γ′ ≡ advertisements Γ ++ advertisements (A auth[ ♯▷ ad ])
    ads≡ rewrite collectFromBase-++ {X = Ad} (Γ ∣ mkRev Δ) (A auth[ ♯▷ ad ])
                | collectFromBase-++ {X = Ad} Γ (mkRev Δ)
                | hᵃ Δ
                | L.++-identityʳ (advertisements Γ)
                = refl

    txout↝ : Γ →⦅ Txout ⦆ Γ′
    -- txout↝ = lift Γ —⟨ ids ⟩— Γ′ ⊣ ids≡
    txout↝ txoutΓ {x} x∈
      with ∈-ids-++⁻ (Γ ∣ mkRev Δ) (A auth[ ♯▷ ad ]) x∈
    ... | inj₂ ()
    ... | inj₁ x∈
      with ∈-ids-++⁻ Γ (mkRev Δ) x∈
    ... | inj₂ x∈ = contradict $ x∈ :~ hʳ Δ ⟪ x L.Mem.∈_ ⟫
      where
      hʳ : ∀ Δ → Null $ ids (mkRev Δ)
      hʳ [] = refl
      hʳ (_ ∷ []) = refl
      hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _
    ... | inj₁ x∈ = txoutΓ x∈

    sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
    sechash↝ sechash′ = extend-↦ (↭-reflexive secrets≡) sechash′ sechash⁺

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ κ′ = extend-↦ (↭-reflexive ads≡) κ′ κ″
      where
        κ″ : advertisements (A auth[ ♯▷ ad ]) ↦′ 𝕂²′
        κ″ x∈ with does (A ∈? Hon) | x∈
        ... | true  | 𝟘 = k⃗
        ... | false | ()
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝
  private
    𝕣′ : ℝ R′
    𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)
  abstract
    value-preserving⇒ :
      ValuePreservingʳ 𝕣
      ───────────────────
      ValuePreservingʳ 𝕣′
    value-preserving⇒ pv-txout = pv-txout′
      where
      open ≡-Reasoning

      txoutR : Txout (R ∙cfg)
      txoutR = 𝕣 ∙txoutEnd_

      txoutΓ : Txout Γ
      txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutR

      pv-txoutΓ : ValuePreserving {Γ} txoutΓ
      pv-txoutΓ = ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) txoutR pv-txout

      txoutΓ′ : Txout Γ′
      txoutΓ′ = txout↝ txoutΓ

      pv↝ : ValuePreserving↝ {Γ}{Γ′} txout↝
      pv↝ txoutΓ pv-txoutΓ {x} x∈
        with ∈-ids-++⁻ (Γ ∣ mkRev Δ) (A auth[ ♯▷ ad ]) x∈
      ... | inj₂ ()
      ... | inj₁ x∈
        with ∈-ids-++⁻ Γ (mkRev Δ) x∈
      ... | inj₂ x∈ = contradict $ x∈ :~ hʳ Δ ⟪ x L.Mem.∈_ ⟫
        where
        hʳ : ∀ Δ → Null $ ids (mkRev Δ)
        hʳ [] = refl
        hʳ (_ ∷ []) = refl
        hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _
      ... | inj₁ x∈ = pv-txoutΓ x∈

      pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
      pv-txoutΓ′ = pv↝ txoutΓ pv-txoutΓ

      txoutΓ″ : Txout Γ″
      txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

      pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
      pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

      pv-txout′ : ValuePreservingʳ 𝕣′
      pv-txout′ x∈ =
        begin
          (𝕣′ ∙txoutEnd x∈) ∙value
        ≡⟨ cong _∙value $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
          (txoutΓ″ x∈) ∙value
        ≡⟨ pv-txoutΓ″ _ ⟩
          (Γ″ , x∈) ∙value
        ∎

data _⨾_⨾_~ℍ[2]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₂-args} {B}
    → let
        -- (i) consume {G}C and its persistent deposits from Rˢ
        open H₂-args h renaming (ad to ⟨G⟩C)

        C      = encodeAd ⟨G⟩C (ad∈⇒Txout {⟨G⟩C}{Γ}{Rˢ} 𝟘 R≈ txout′)
        C,h̅,k̅  = encode (C , h̅ , k̅)
        C,h̅,k̅ₐ = SIG (K A) C,h̅,k̅

        -- (ii) broadcast message in Rᶜ
        λᶜ = B →∗∶ C,h̅,k̅ₐ

        -- (v) txout = txout′ (vi) extend sechash′ (vii) extend κ′
        open H₂ h using (λˢ)
      in

      -- (i) ⟨G⟩C has been previously advertised in Rᶜ
    ∀ (∃B : ∃ λ B → (B →∗∶ C) ∈ toList Rᶜ) →

      -- ∘ it is the first occurrence of such a broadcast in Rᶜ
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ C) (Any-tail $ ∃B .proj₂)

      -- ∘ hashes respect security parameter η
    ∙ All (λ hᵢ → ∣ hᵢ ∣ᵐ ≡ η) h̅

      -- ∘ make sure that λᶜ is the first occurrence of such a message after C in Rᶜ
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)

      -- (iii) each hᵢ is obtained by querying the oracle,
      --       otherwise we have a dishonestly chosen secret
    ∙ CheckOracleInteractions Rᶜ Δ×h̅

      -- (iv) no hash is reused
    ∙ Unique h̅
    ∙ Disjoint h̅ (codom sechash′)

      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[2]~ λᶜ ⨾ Rᶜ

-- ** Stipulation: authorizing deposits
record H₃-args : Type where
  constructor mk
  field
    {ad Γ₀ t A x v} : _
  open ∣AD ad public
  field
    -- Hypotheses from [C-AuthInit]
    committedA : partG ⊆ committedParticipants ad Γ₀
    A∈per : (A , v , x) ∈ persistentDeposits G
  open Transition
    ( (` ad ∣ Γ₀) ⨾ t
    —— auth-init⦅ A , ad , x ⦆ —→
      (` ad ∣ Γ₀ ∣ A auth[ x ▷ˢ ad ]) ⨾ t
    ⊣ Act ([C-AuthInit] committedA A∈per)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₃ (⋯ : H₃-args) (let open H₃-args ⋯) where
  private
    𝕘 : 𝔾 ad
    𝕘 = LIFT₀ 𝕣 t Γ R≈ ad 𝟘 committedA
  T : ∃Tx
  T = -, -, COMPILE-INIT 𝕘
  private
    names≡ : Γ′ ≡⦅ names ⦆ Γ
    names≡ rewrite collectFromBase-++ {X = Name} Γ (A auth[ x ▷ˢ ad ])
                  = L.++-identityʳ _

    ids≡ : Γ′ ≡⦅ ids ⦆ Γ
    ids≡ = cong filter₂ names≡

    secrets≡ : Γ′ ≡⦅ secrets ⦆ Γ
    secrets≡ = cong filter₁ names≡

    ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
    ads≡ rewrite collectFromBase-++ {X = Ad} Γ (A auth[ x ▷ˢ ad ])
                = L.++-identityʳ _

    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ txout′ rewrite ids≡ = txout′

    sechash↝ : Γ →⦅ Sechash ⦆ Γ′
    sechash↝ sechash′ rewrite secrets≡ = sechash′

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ κ′ rewrite collectFromBase-++ {X = Ad} Γ (A auth[ x ▷ˢ ad ])
                | L.++-identityʳ (advertisements Γ)
                = κ′
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝

data _⨾_⨾_~ℍ[3]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₃-args} {B}
    → let
        -- (i) consume {G}C and its persistent deposits from Rˢ
        open H₃-args h

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        open H₃ h using (λˢ; T)

        -- (i) broadcast Tᵢₙᵢₜ , signed with A's private key
        m = SIG (K̂ A) T
        λᶜ = B →∗∶ m
      in

      -- (ii) Tᵢₙᵢₜ occurs as a message in Rᶜ
    ∀ (∃B : ∃ λ B → B →∗∶ encode (T .proj₂ .proj₂) ∈ toList Rᶜ) →

      -- (iii) broadcast message in Rᶜ
      -- ∘ λᶜ is the first occurrence of such a message after Tinit in Rᶜ
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃B .proj₂)

      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[3]~ λᶜ ⨾ Rᶜ

-- ** Stipulation: activating the contract
record H₄-args : Type where
  constructor mk
  field
    {ad Γ₀ t z} : _
  open ∣AD ad public
  ds = persistentDeposits G
  vs = map select₂ ds
  xs = map select₃ ds
  v  = sum vs
  field
    -- Hypotheses from [C-Init]
    fresh-z : z ∉ xs ++ ids Γ₀
  Γ₁ = Cfg ∋ ` ad ∣ Γ₀
  Γ₂ = Cfg ∋ || map (λ{ (Aᵢ , vᵢ , xᵢ) →
    ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds
  Γ₃ = Cfg ∋ || map (_auth[ ♯▷ ad ]) partG
  open Transition
    ( (Γ₁ ∣ Γ₂ ∣ Γ₃) ⨾ t
    —— init⦅ G , C ⦆ —→
      (⟨ C , v ⟩at z ∣ Γ₀) ⨾ t
    ⊣ Act ([C-Init] fresh-z)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₄ (⋯ : H₄-args) (let open H₄-args ⋯) where
  private
    committedA : partG ⊆ committedParticipants ad Γ
    committedA {p} p∈ =
      ∈-collect-++⁺ʳ (Γ₁ ∣ Γ₂) Γ₃ ⦃ ∣committedParticipants∣.go ad ⦄ p∈′
      where p∈′ : p ∈ committedParticipants ad Γ₃
            p∈′ rewrite committedPartG≡ {ad} partG = p∈

    𝕘 : 𝔾 ad
    𝕘 = LIFT₀ 𝕣 t Γ R≈ ad 𝟘 committedA
  T : InitTx G
  T = COMPILE-INIT 𝕘
  private
    mkAuth : DepositRefs → Cfg
    mkAuth = ||_
            ∘ map λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }

    h₀ : ∀ ps → Null $ ids (|| map (_auth[ ♯▷ ad ]) ps)
    h₀ [] = refl
    h₀ (_ ∷ []) = refl
    h₀ (_ ∷ ps@(_ ∷ _)) = h₀ ps

    h₀′ : ∀ (ds : DepositRefs) → ids (mkAuth ds) ≡ map select₃ ds
    h₀′ [] = refl
    h₀′ (_ ∷ []) = refl
    h₀′ ((Aᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) =
      begin
        ids ((⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ∣ Δ)
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₂
          (⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) Δ ⟩
        ids (⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ++ ids Δ
      ≡⟨ cong (_++ ids Δ) $ mapMaybe∘collectFromBase-++ isInj₂
          (⟨ Aᵢ has vᵢ ⟩at xᵢ) (Aᵢ auth[ xᵢ ▷ˢ ad ]) ⟩
        (xᵢ ∷ ids (Aᵢ auth[ xᵢ ▷ˢ ad ])) ++ ids Δ
      ≡⟨ cong (λ x → (xᵢ ∷ x) ++ ids Δ) (L.++-identityʳ _) ⟩
        xᵢ ∷ ids Δ
      ≡⟨ cong (xᵢ ∷_) (h₀′ ds) ⟩
        xᵢ ∷ map select₃ ds
      ∎ where open ≡-Reasoning; Δ = mkAuth ds

    h₁ : ∀ (xs : DepositRefs) → Null $ secrets (mkAuth xs)
    h₁ [] = refl
    h₁ (_ ∷ []) = refl
    h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

    h₂ : ∀ xs → Null $ secrets (|| map (_auth[ ♯▷ ad ]) xs)
    h₂ [] = refl
    h₂ (_ ∷ []) = refl
    h₂ (_ ∷ xs@(_ ∷ _)) = h₂ xs

    h₁′ : ∀ (xs : DepositRefs) → Null $ advertisements (mkAuth xs)
    h₁′ [] = refl
    h₁′ (_ ∷ []) = refl
    h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

    ids≡ : ids Γ ≡ ids Γ₀ ++ map select₃ ds
    ids≡ = begin
      ids Γ                    ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ (Γ₁ ∣ Γ₂) Γ₃ ⟩
      ids (Γ₁ ∣ Γ₂) ++ ids Γ₃  ≡⟨ cong (ids (Γ₁ ∣ Γ₂) ++_) (h₀ partG) ⟩
      ids (Γ₁ ∣ Γ₂) ++ []      ≡⟨ L.++-identityʳ _ ⟩
      ids (Γ₁ ∣ Γ₂)            ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ₁ Γ₂ ⟩
      ids Γ₁ ++ ids Γ₂         ≡⟨ cong (_++ ids Γ₂)
                                    $ mapMaybe∘collectFromBase-++ isInj₂ (` ad) Γ₀ ⟩
      ids Γ₀ ++ ids Γ₂         ≡⟨ cong (ids Γ₀ ++_) (h₀′ ds) ⟩
      ids Γ₀ ++ map select₃ ds ∎ where open ≡-Reasoning

    secrets≡ : Γ′ ≡⦅ secrets ⦆ Γ
    secrets≡ = sym $ begin
      secrets Γ                       ≡⟨⟩
      secrets (Γ₁ ∣ Γ₂ ∣ Γ₃)          ≡⟨ mapMaybe∘collectFromBase-++ isInj₁
                                           (Γ₁ ∣ Γ₂) Γ₃ ⟩
      secrets (Γ₁ ∣ Γ₂) ++ secrets Γ₃ ≡⟨ cong (secrets (Γ₁ ∣ Γ₂)  ++_) (h₂ partG) ⟩
      secrets (Γ₁ ∣ Γ₂) ++ []         ≡⟨ L.++-identityʳ _ ⟩
      secrets (Γ₁ ∣ Γ₂)               ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ Γ₁ Γ₂ ⟩
      secrets Γ₁ ++ secrets Γ₂        ≡⟨ cong (secrets Γ₁ ++_) (h₁ ds) ⟩
      secrets Γ₁ ++ []                ≡⟨ L.++-identityʳ _ ⟩
      secrets Γ₁                      ≡⟨⟩
      secrets Γ′                      ∎ where open ≡-Reasoning

    ads⊆′ : Γ′ ⊆⦅ advertisements ⦆ Γ
    ads⊆′ = begin
      advertisements Γ′ ≡⟨⟩
      advertisements Γ₀ ⊆⟨ ∈-collect-++⁺ˡ (Γ₁ ∣ Γ₂) Γ₃ ∘ ∈-collect-++⁺ˡ Γ₁ Γ₂ ⟩
      advertisements Γ  ∎ where open ⊆-Reasoning Ad

    sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
    sechash↝ = lift Γ —⟨ secrets ⟩— Γ′ ⊣ secrets≡

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ κ′ = weaken-↦ κ′ ads⊆′

    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ txout′
      rewrite ids≡
      = cons-↦ z ((-, -, T) at 0)
      $ weaken-↦ txout′ ∈-++⁺ˡ
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝

data _⨾_⨾_~ℍ[4]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₄-args}
    → let
        -- (i) consume {G}C and its persistent deposits from Rˢ
        open H₄-args h

        -- (iii) sechash = sechash′, κ = κ′, txout extends txout′ with (z ↦ Tᵢₙᵢₜ)
        open H₄ h using (λˢ; T)

        -- (ii) append Tᵢₙᵢₜ to the blockchain
        λᶜ = submit (-, -, T)

      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[4]~ λᶜ ⨾ Rᶜ

-- ** Contract actions: authorize control
record H₅-args : Type where
  constructor mk
  field
    {c v x Γ₀ t A} : _
    {i} : Index c
  open ∣SELECT c i public
  field
    -- D ≡ A ∶ D′
    D≡A:D′ : A ∈ authDecorations d
    -- Hypotheses from [C-AuthControl], already in hypothesis `D≡A:D′`
  open Transition
    ( (⟨ c , v ⟩at x ∣ Γ₀) ⨾ t
      —— auth-control⦅ A , x ▷ d ⦆ —→
      (⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀) ⨾ t
    ⊣ Act ([C-AuthControl] D≡A:D′)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₅ (⋯ : H₅-args) (let open H₅-args ⋯) where
  private
    -- (ii) {G}C is the ancestor of ⟨C, v⟩ₓ in Rˢ
    T×K = COMPILE-ANCESTOR {Γ = Γ} {i = i} R≈ 𝟘 𝕣

  T : BranchTx (d ∗)
  T = T×K .proj₁

  Kᵈ : KeyPair
  Kᵈ = T×K .proj₂ D≡A:D′

  -- (iv) txout = txout′, sechash = sechash′, κ = κ′
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id

data _⨾_⨾_~ℍ[5]~_⨾_ : StepRel where
  mkℍ :
    -- (i) Rˢ contains ⟨C , v⟩ₓ with C = D + ∑ᵢ Dᵢ
    ∀ {h : H₅-args} (open H₅-args h)
      {B : Participant}
    → let
        open H₅ h using (λˢ; Kᵈ; T)
        λᶜ = B →∗∶ SIG Kᵈ (∃Tx ∋ -, -, T)
      in
        Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[5]~ λᶜ ⨾ Rᶜ

-- ** Contract actions: put
record H₆-args : Type where
  constructor mk
  field
    {c v y c′ y′ Γ₀ t p} : _
    {ds} : DepositRefs
    {ss} : List (Participant × Secret × ℕ)
    {i} : Index c
  vs = unzip₃ ds .proj₂ .proj₁
  xs = unzip₃ ds .proj₂ .proj₂ -- (i) xs = x₁⋯xₖ
  as = unzip₃ ss .proj₂ .proj₁
  Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
  Δ   = || map (uncurry₃ _∶_♯_) ss
  Γ₂  = Cfg ∋ Δ ∣ Γ₀
  Γ₁₂ = Cfg ∋ Γ₁ ∣ Γ₂
  open ∣SELECT c i public
  As = decorations d .proj₁
  ts = decorations d .proj₂
  field
    -- ii) in Rˢ, α consumes ⟨D+C,v⟩y and the deposits ⟨Aᵢ,vᵢ⟩ₓᵢ
    -- to produce ⟨C′,v′⟩y′
    --     where D = ⋯ : put⋯reveal⋯.C′
    --     let t be the maximum deadline in an `after` in front of D
    --     T0D0: what should t′ be in case there are no `after` decorations?
    --           (currently any value)
    t≡ : t ≡ maximum t ts
    d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′
    -- Hypotheses from [C-PutRev]
    fresh-y′ : y′ ∉ y L.∷ ids Γ₁₂
    p⟦Δ⟧≡ : ⟦ p ⟧ᵖ Δ ≡ just true
    -- Hypotheses from [Timeout]
    As≡∅ : Null As


  private
    α  = put⦅ xs , as , y ⦆
    Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂

    ∀≤t : All (_≤ t) ts
    ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

    put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
    put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡
           ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

  open Transition
    ( (⟨ c , v ⟩at y ∣ Γ₁₂) ⨾ t —— α —→ Γ′ ⨾ t
    ⊣ [Timeout] As≡∅ ∀≤t put→ refl
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₆ (⋯ : H₆-args) (let open H₆-args ⋯) where
  T : Tx (suc $ length xs) 1
  T = COMPILE-ANCESTOR {Γ = Γ} {i = i} R≈ 𝟘 𝕣 .proj₁ :~ d≡ ⟪ BranchTx ⟫

  private
    txi : TxInput′
    txi = (-, -, T) at 0

    postulate val≡ : txi ∙value ≡ v + sum vs

    open ≡-Reasoning

    secrets≡ : Γ′ ≡⦅ namesˡ ⦆ Γ
    secrets≡ =
      begin
        namesˡ Γ′
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ (⟨ c′ , v + sum vs ⟩at y′) Γ₂ ⟩
        namesˡ (⟨ c′ , v + sum vs ⟩at y′) ++ namesˡ Γ₂
      ≡⟨⟩
        namesˡ Γ₂
      ≡˘⟨ L.++-identityˡ _ ⟩
        [] ++ namesˡ Γ₂
      ≡˘⟨ cong (_++ namesˡ Γ₂) (go ds) ⟩
        namesˡ (⟨ c′ , v ⟩at y ∣ Γ₁) ++ namesˡ Γ₂
      ≡˘⟨ mapMaybe∘collectFromBase-++ isInj₁ (⟨ c′ , v ⟩at y ∣ Γ₁) Γ₂ ⟩
        namesˡ Γ
      ∎ where
        go : ∀ (ds : DepositRefs) →
          Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
        go [] = refl
        go (_ ∷ []) = refl
        go (_ ∷ xs@(_ ∷ _)) = go xs

    ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
    ads≡ =
      begin
        advertisements Γ′
      ≡⟨⟩
        advertisements Γ₂
      ≡˘⟨ cong (_++ advertisements Γ₂) (go ds) ⟩
        advertisements Γ₁ ++ advertisements Γ₂
      ≡⟨ sym $ collectFromBase-++ Γ₁ Γ₂ ⟩
        advertisements Γ
      ∎ where
        go : ∀ (ds : DepositRefs) →
          Null $ advertisements (|| map (uncurry₃ ⟨_has_⟩at_) ds)
        go [] = refl
        go (_ ∷ []) = refl
        go (_ ∷ xs@(_ ∷ _)) = go xs

    sechash↝ :  Γ →⦅ Sechash ⦆ Γ′
    sechash↝ = lift Γ —⟨ namesˡ ⟩— Γ′ ⊣ secrets≡

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡

    p⊆ : Γ₂ ⊆⦅ ids ⦆ Γ
    p⊆ = there ∘ ∈-ids-++⁺ʳ Γ₁ Γ₂

    -- (v) extend txout′ with {y′↦(T,0)}, sechash = sechash′, κ = κ′
    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ txout′ = cons-↦ y′ txi $ weaken-↦ txout′ p⊆
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝
  private
    𝕣′ : ℝ R′
    𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)
  abstract
    value-preserving⇒ :
      ValuePreservingʳ 𝕣
      ───────────────────
      ValuePreservingʳ 𝕣′
    value-preserving⇒ pv-txout = pv-txout′
      where
      txoutΓ : Txout Γ
      txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

      pv-txoutΓ : ValuePreserving {Γ} txoutΓ
      pv-txoutΓ =
        ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

      txoutΓ₂ : Txout Γ₂
      txoutΓ₂ = weaken-↦ txoutΓ p⊆

      pv-txoutΓ₂ : ValuePreserving {Γ₂} txoutΓ₂
      pv-txoutΓ₂ x∈ =
        begin
          txoutΓ₂ x∈ ∙value
        ≡⟨⟩
          weaken-↦ txoutΓ p⊆ x∈ ∙value
        ≡⟨ pv-weaken-↦ {Γ}{Γ₂} txoutΓ p⊆ pv⊆ pv-txoutΓ x∈ ⟩
          (Γ₂ , x∈) ∙value
        ∎ where open ≡-Reasoning
                pv⊆ : ValuePreserving⊆ {Γ₂}{Γ} p⊆
                pv⊆ x∈ =
                  begin
                    (Γ₂ , x∈) ∙value
                  ≡˘⟨ ∈-ids-++⁺ʳ∙value {Γ′ = Γ₂}{Γ₁} x∈ ⟩
                    (Γ₁ ∣ Γ₂ , ∈-ids-++⁺ʳ Γ₁ Γ₂ x∈) ∙value
                  ≡⟨⟩
                    (Γ , there (∈-ids-++⁺ʳ Γ₁ Γ₂ x∈)) ∙value
                  ≡⟨⟩
                    (Γ , p⊆ x∈) ∙value
                  ∎

      txoutΓ′ : Txout Γ′
      txoutΓ′ = txout↝ txoutΓ

      pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
      pv-txoutΓ′ = pv-cons-↦ val≡ pv-txoutΓ₂

      txoutΓ″ : Txout Γ″
      txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

      pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
      pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

      pv-txout′ : ValuePreservingʳ 𝕣′
      pv-txout′ x∈ =
        begin
          (𝕣′ ∙txoutEnd x∈) ∙value
        ≡⟨ cong _∙value
              $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
          (txoutΓ″ x∈) ∙value
        ≡⟨ pv-txoutΓ″ _ ⟩
          (Γ″ , x∈) ∙value
        ∎

data _⨾_⨾_~ℍ[6]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₆-args} (open H₆-args h) →
    let
      open H₆ h using (λˢ; T)
      λᶜ = submit (-, -, T)
    in
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[6]~ λᶜ ⨾ Rᶜ

-- ** Contract actions: authorize reveal
record H₇-args : Type where
  constructor mk
  field
    {ad A a n Γ₀ t} : _
    k⃗   : 𝕂²′ ad
    Δ×h̅ : List (Secret × Maybe ℕ × ℤ)
  open ∣AD ad public
  Δ = map drop₃   Δ×h̅
  h̅ = map select₃ Δ×h̅
  k̅ = concatMap (map pub ∘ codom) (codom k⃗)
  open Transition
    ( (⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀) ⨾ t —— auth-rev⦅ A , a ⦆ —→ A ∶ a ♯ n ∣ Γ₀ ⨾ t
    ⊣ Act [C-AuthRev]
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public
  field
    -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
    ∃α : auth-commit⦅ A , ad , Δ ⦆ ∈ labelsʳ R

module H₇ (⋯ : H₇-args) (let open H₇-args ⋯) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id

  txoutᶜ : Txout ad × Txout C
  txoutᶜ = auth-commit∈⇒Txout ∃α 𝕣

  𝕣∗′ : ℝ∗ Rˢ′
  𝕣∗′ = Γₜ″ ∷ 𝕣∗ ⊣ 𝕒 , λˢ ✓

data _⨾_⨾_~ℍ[7]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₇-args} {B} {mˢ : String} (let m = encode mˢ)
    → let
        open H₇-args h renaming (ad to ⟨G⟩C)

        a∈R : a ∈ secrets Rˢ
        a∈R = namesˡ⦅end⦆⊆ Rˢ
            $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ R≈ .proj₂) 𝟘

        -- (iii) txout = txout′, sechash = sechash′, κ = κ′
        open H₇ h using (λˢ; txoutᶜ; 𝕣∗′)
        -- (i) some participant B broadcasts message m
        λᶜ = B →∗∶ m
      in
      -- ... with a corresponding broadcast of m′=(C,h̅,k̅) in Rᶜ
      -- T0D0: should we search for a signature of this message instead?
    ∀ (∃λ : ∃ λ B → ∃ λ txoutᶜ →
          let C,h̅,k̅ = encode (encodeAd ⟨G⟩C txoutᶜ , h̅ , k̅)
          in  B →∗∶ SIG (K B) C,h̅,k̅ ∈ toList Rᶜ) →

    ∙ a ∈ secrets G
    ∙ ∣ m ∣ᵐ ≥ η

      -- (ii) in Rᶜ we find ⋯ (B → O ∶ m) (O → B : sechash′(a)) for some B ⋯
    ∙ (∃ λ B → (B , m , sechash′ {a} a∈R) ∈ oracleInteractionsᶜ Rᶜ)

      -- (v) λᶜ is the first broadcast of m after the first broadcast of m′
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃λ .proj₂ .proj₂)

      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[7]~ λᶜ ⨾ Rᶜ

-- ** Contract actions: split
record H₈-args : Type where
  constructor mk
  field
    {c y Γ₀ t} : _
    {i} : Index c
    {vcis} : VIContracts
  open ∣SELECT c i public
  vs  = unzip₃ vcis .proj₁
  v   = sum vs
  cs  = unzip₃ vcis .proj₂ .proj₁
  vcs = zip vs cs
  xs  = unzip₃ vcis .proj₂ .proj₂
  As = decorations d .proj₁
  ts = decorations d .proj₂
  field
    -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨C₀,v₀⟩ₓ₀ | ⋯ | ⟨Cₖ,vₖ⟩ₓₖ
    --     where D = ⋯ : split vs → cs
    --     let t be the maximum deadline in an `after` in front of D
    --     T0D0: what should t′ be in case there are not after decorations?
    --           (currently any value)
    t≡ : t ≡ maximum t ts
    d≡ : d ≡⋯∶ split vcs
    -- Hypotheses from [C-Split]
    fresh-xs : All (_∉ y L.∷ ids Γ₀) xs
    -- Hypotheses from [Timeout]
    As≡∅ : Null As
  Γ₁ = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis
  private
    α  = split⦅ y ⦆
    Γ′ = Γ₁ ∣ Γ₀

    ∀≤t : All (_≤ t) ts
    ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

    split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
    split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
          ~: [C-Split] {vcis = vcis} fresh-xs
  open Transition
    ( (⟨ c , v ⟩at y ∣ Γ₀) ⨾ t —— α —→ Γ′ ⨾ t
    ⊣ [Timeout] As≡∅ ∀≤t split→ refl
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₈ (⋯ : H₈-args) (let open H₈-args ⋯) where
  -- (iii) submit transaction T
  --       where ∙ (T′,o) = txout′(y)
  --             ∙ T is the first transaction in Bpar(cs,d,T′,o,partG,t)
  --       i.e. the one corresponding to subterm `d∗ = split (zip vs cs)`
  T : Tx 1 (length xs)
  T =
    let
        open ≡-Reasoning
        vs≡ , cs≡ , xs≡ = length-unzip₃ vcis

        l≡ : length xs ≡ length (zip vs cs)
        l≡ = sym $
          begin length (zip vs cs)    ≡⟨ L.length-zipWith _,_ vs cs ⟩
                length vs ⊓ length cs ≡⟨ Nat.m≥n⇒m⊓n≡n
                                        $ Nat.≤-reflexive $ trans cs≡ (sym vs≡) ⟩
                length cs             ≡⟨ cs≡ ⟩
                length vcis           ≡⟨ sym xs≡ ⟩
                length xs             ∎
    in
      ⟪ Tx 1 ⟫ l≡
         -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
      ~: ( COMPILE-ANCESTOR {Γ = Γ} {i = i} R≈ 𝟘 𝕣 .proj₁
         :~ d≡ ⟪ BranchTx ⟫)
  private
    -- (iv) extend txout′ with {xᵢ ↦ (T,i)}, sechash = sechash′, κ = κ′
    txout⁺ : xs ↦ TxInput′
    txout⁺ x∈ = (-, -, T) at L.Any.index x∈

    hʳ : ∀ (vcis : VIContracts) →
        ids (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
      ≡ (proj₂ $ proj₂ $ unzip₃ vcis)
    hʳ [] = refl
    hʳ (_ ∷ []) = refl
    hʳ (_ ∷ xs@(_ ∷ _)) = cong (_ ∷_) (hʳ xs)

    hˡ : ∀ (vcis : VIContracts) →
      Null $ secrets (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
    hˡ [] = refl
    hˡ (_ ∷ []) = refl
    hˡ (_ ∷ xs@(_ ∷ _)) = hˡ xs

    hᵃ : ∀ (vcis : VIContracts) →
      Null $ advertisements (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
    hᵃ [] = refl
    hᵃ (_ ∷ []) = refl
    hᵃ (_ ∷ xs@(_ ∷ _)) = hᵃ xs

    ids≡ : ids Γ ≡ y ∷ ids Γ₀
    ids≡ = mapMaybe∘collectFromBase-++ isInj₂ (⟨ c , v ⟩at y) Γ₀

    ids≡′ : ids Γ′ ≡ xs ++ ids Γ₀
    ids≡′ =
      begin
        ids Γ′
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₂ Γ₁ Γ₀ ⟩
        ids Γ₁ ++ ids Γ₀
      ≡⟨ cong (_++ ids Γ₀) (hʳ vcis) ⟩
        xs ++ ids Γ₀
      ∎ where open ≡-Reasoning

    secrets≡ : Γ′ ≡⦅ secrets ⦆ Γ
    secrets≡ =
      begin
        secrets Γ′
      ≡⟨ mapMaybe∘collectFromBase-++ isInj₁ Γ₁ Γ₀ ⟩
        secrets Γ₁ ++ secrets Γ₀
      ≡⟨ cong (_++ secrets Γ₀) (hˡ vcis) ⟩
        secrets Γ₀
      ≡⟨⟩
        secrets Γ
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
    txout↝ txout′ rewrite ids≡
      = extend-↦ (↭-reflexive ids≡′) txout⁺ (weaken-↦ txout′ there)

    sechash↝ : Γ →⦅ Sechash ⦆ Γ′
    sechash↝ = lift Γ —⟨ secrets ⟩— Γ′ ⊣ secrets≡

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝

data _⨾_⨾_~ℍ[8]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₈-args}
    → let
        open H₈-args h
        open H₈ h using (λˢ; T)
        λᶜ = submit (-, -, T)
      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[8]~ λᶜ ⨾ Rᶜ

-- ** Contract actions: withdraw
record H₉-args : Type where
  constructor mk
  field
    {c v y Γ₀ A x t} : _
    {i} : Index c
  open ∣SELECT c i public
  As = decorations d .proj₁
  ts = decorations d .proj₂
  field
    -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨A,v⟩ₓ (where D = ⋯ : withdraw A)
    d≡ : d ≡⋯∶ withdraw A
    -- Hypotheses from [C-Withdraw]
    fresh-x : x ∉ y L.∷ ids Γ₀
    -- Hypotheses from [Timeout]
    As≡∅ : Null As
    ∀≤t : All (_≤ t) ts
  private
    α  = withdraw⦅ A , v , y ⦆
    Γ′ = ⟨ A has v ⟩at x ∣ Γ₀
  open Transition
    ( (⟨ c , v ⟩at y ∣ Γ₀) ⨾ t —— α —→ Γ′ ⨾ t
    ⊣ [Timeout] As≡∅ ∀≤t
        (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x)
        refl
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₉ (⋯ : H₉-args) (let open H₉-args ⋯) where
  -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
  --   ∙ T′ at o = txout′(x)
  --   ∙ T is the first transaction of Bd(d,d,T′,o,v,partG,0)
  -- i.e.
  -- (iii) submit transaction T
  --       where ∙ (T′,o) = txout′(y)
  --             ∙ T is the first transaction in Bd(d,d,T′,o,v,partG,0)
  --       i.e. the one corresponding to subterm `d∗ = withdraw A`
  T : ∃Tx
  T = -, -, COMPILE-ANCESTOR {Γ = Γ} {i = i} R≈ 𝟘 𝕣 .proj₁ :~ d≡ ⟪ BranchTx ⟫
  private
    -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝  txout′
      = cons-↦ x (T at 0)
      $ weaken-↦ txout′ there
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ id id

  -- 𝕣∗′ : ℝ∗ Rˢ′
  -- 𝕣∗′ = Γₜ″ ∷ 𝕣∗ ⊣ 𝕒 , λˢ ✓

data _⨾_⨾_~ℍ[9]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₉-args}
    → let
        open H₉-args h
        open H₉ h using (λˢ; T)
        -- open H₉ h using (𝕣∗′; T)
        λᶜ = submit T
      in
      ─────────────────────────────────────────
      -- Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[9]~ λᶜ ⨾ Rᶜ
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[9]~ λᶜ ⨾ Rᶜ

-- ** Deposits: authorize join
record H₁₀-args : Type where
  constructor mk
  field
    {A v x v′ x′ Γ₀ t} : _
  open Transition
    ( (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀) ⨾ t
      —— auth-join⦅ A , x ↔ x′ ⦆ —→
      ( ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′
      ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀) ⨾ t
    ⊣ Act [DEP-AuthJoin]
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₀ (⋯ : H₁₀-args) (let open H₁₀-args ⋯) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id

data _⨾_⨾_~ℍ[10]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₀-args} {B}
    → let
        open H₁₀-args h

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ
            ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
      in
    ∀ (∃B : ∃ λ B → ∃ λ (T : Tx 2 1) →
         (B →∗∶ encode T ∈ toList Rᶜ)
       × (T .inputs  ≡ (hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]))
       × (T .outputs ≡ [ (v + v′) redeemable-by K̂ A ]))
    → let
        -- (iii) broadcast transaction T, signed by A
        _ , T , B∈ , _  = ∃B
        m′ = SIG (K̂ A) (∃Tx ∋ -, -, T)
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₀ h using (λˢ)
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front B∈)
      ────────────────────────────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[10]~ λᶜ ⨾ Rᶜ

-- ** Deposits: join
record H₁₁-args : Type where
  constructor mk
  field
    {A v x v′ x′ y Γ₀ t} : _
    -- Hypotheses from [DEP-Join]
    fresh-y : y ∉ x L.∷ x′ ∷ ids Γ₀
  open Transition
    ( ( ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′
      ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀) ⨾ t
      —— join⦅ x ↔ x′ ⦆ —→
      (⟨ A has (v + v′) ⟩at y ∣ Γ₀) ⨾ t
    ⊣ Act ([DEP-Join] fresh-y)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₁ (⋯ : H₁₁-args) (let open H₁₁-args ⋯) (tx : TxInput′) where
  private
    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ (λ x∈ → there (there x∈))

    -- Γ″  = ∃Γ≈ .proj₁
    -- Γₜ″ = Γ″ at t′

  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ id id

  -- private
  --   𝕣′ : ℝ R′
  --   𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)

  -- module _ {c v x} where
  --   private
  --     c∈⇐ : R′ ≈⋯ ⟨ c , v ⟩at x ⋯
  --         → R  ≈⋯ ⟨ c , v ⟩at x ⋯
  --     c∈⇐ = ?
    -- abstract
    --   txoutEndC≡ : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ″) →
    --     𝕣′ ∙txoutC c∈ ≡ 𝕣 ∙txoutC (c∈⇐ c∈)
    --   txoutEndC≡ c∈ =
    --     begin
    --       𝕣′ ∙txoutC c∈
    --     ≡⟨⟩
    --       𝕣′ ∙txoutEnd (c∈⇒x∈ (R′ ∙cfg) c∈)
    --     -- ≡⟨ cong (𝕣′ ∙txoutEnd_) $ sym $ H c∈ ⟩
    --     --   𝕣′ ∙txoutEnd (x∈⇒ $ c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
    --     -- ≡⟨ txoutEnd≡ (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈) ⟩
    --     --   𝕣 ∙txoutEnd (c∈⇒x∈ (R ∙cfg) $ c∈⇐ c∈)
    --     ≡⟨ ? ⟩
    --       𝕣 ∙txoutC (c∈⇐ c∈)
    --     ∎ where open ≡-Reasoning

data _⨾_⨾_~ℍ[11]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₁-args}
    → let
        open H₁₁-args h

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ
            ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

        -- (ii) submit transaction T
        T : ∃Tx
        T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ (v + v′) redeemable-by K̂ A ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (iii) extend txout′ with y↦T₀ (removing {x↦_;x′↦_}),
        --       sechash = sechash′, κ = κ′
        open H₁₁ h (T at 0) using (λˢ)
      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[11]~ λᶜ ⨾ Rᶜ

-- ** Deposits: authorize divide (similar to [10])
record H₁₂-args : Type where
  constructor mk
  field
    {A v v′ x Γ₀ t} : _
  open Transition
    ( (⟨ A has (v + v′) ⟩at x ∣ Γ₀) ⨾ t
      —— auth-divide⦅ A , x ▷ v , v′ ⦆ —→
      (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀) ⨾ t
    ⊣ Act [DEP-AuthDivide]
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₂ (⋯ : H₁₂-args) (let open H₁₂-args ⋯) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id

data _⨾_⨾_~ℍ[12]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₂-args} {B}
    → let
        open H₁₂-args h

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ
            ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
      in
    ∀ (∃B : ∃ λ B → ∃ λ (T : Tx 1 2) →
         (B →∗∶ encode T ∈ toList Rᶜ)
       × (T .inputs  ≡ [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ])
       × (T .outputs ≡ [ v redeemable-by K̂ A ⨾ v′ redeemable-by K̂ A ]))
    → let
        -- (iii) broadcast transaction T, signed by A
        _ , T , B∈ , _ = ∃B
        m′ = SIG (K̂ A) (∃Tx ∋ -, -, T)
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₂ h using (λˢ)
      in

    -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front B∈)

      ─────────────────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[12]~ λᶜ ⨾ Rᶜ

-- ** Deposits: divide (similar to [11])
record H₁₃-args : Type where
  constructor mk
  field
    {A v v′ x Γ₀ y y′ t} : _
  field
    -- Hypotheses from [DEP-Divide]
    fresh-ys : All (_∉ x L.∷ ids Γ₀ ) [ y ⨾ y′ ]
  open Transition
    ( (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀) ⨾ t
      —— divide⦅ x ▷ v , v′ ⦆ —→
      (⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀) ⨾ t
    ⊣ Act ([DEP-Divide] fresh-ys)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₃ (⋯ : H₁₃-args) (let open H₁₃-args ⋯) (tx tx′ : TxInput′) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ id id
    where txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝ txout′ = cons-↦ y tx $ cons-↦ y′ tx′ $ weaken-↦ txout′ there

data _⨾_⨾_~ℍ[13]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₃-args}
    → let
        open H₁₃-args h

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆ = namesʳ⦅end⦆⊆ Rˢ
           ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

        -- (iii) submit transaction T
        T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ v redeemable-by K̂ A ⨾ v′ redeemable-by K̂ A ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (v) extend txout′ with {y↦T₀, y′↦T₁} (removing x↦T₀),
        --     sechash = sechash′, κ = κ′
        open H₁₃ h (T at 0) (T at 1) using (λˢ)
      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[13]~ λᶜ ⨾ Rᶜ

-- ** Deposits: authorize donate (similar to [10])
record H₁₄-args : Type where
  constructor mk
  field
    {A v x Γ₀ B′ t} : _
  open Transition
    ( (⟨ A has v ⟩at x ∣ Γ₀) ⨾ t
      —— auth-donate⦅ A , x ▷ᵈ B′ ⦆ —→
      (⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀) ⨾ t
    ⊣ Act [DEP-AuthDonate]
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₄ (⋯ : H₁₄-args) (let open H₁₄-args ⋯) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id

data _⨾_⨾_~ℍ[14]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₄-args} {B}
    → let
        open H₁₄-args h

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ
            ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
      in
    ∀ (∃B : ∃ λ B → ∃ λ (T : Tx 1 1) →
         (B →∗∶ encode T ∈ toList Rᶜ)
       × (T .inputs  ≡ [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ])
       × (T .outputs ≡ [ v redeemable-by K̂ B′ ]))
    → let
        -- (iii) broadcast transaction T, signed by A
        _ , T , B∈ , _ = ∃B
        m′ = SIG (K̂ A) (∃Tx ∋ -, -, T)
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₄ h using (λˢ)
      in

    -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front B∈)

      ──────────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[14]~ λᶜ ⨾ Rᶜ

-- ** Deposits: donate (similar to [11])
record H₁₅-args : Type where
  constructor mk
  field
    {A v x B′ Γ₀ y t} : _
  field
    -- Hypotheses from [DEP-Donate]
    fresh-y : y ∉ x L.∷ ids Γ₀
  open Transition
    ( (⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀) ⨾ t
      —— donate⦅ x ▷ᵈ B′ ⦆ —→
      (⟨ B′ has v ⟩at y ∣ Γ₀) ⨾ t
    ⊣ Act ([DEP-Donate] fresh-y)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₅ (⋯ : H₁₅-args) (let open H₁₅-args ⋯) (tx : TxInput′) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ id id
    where txout↝ : Γ →⦅ Txout ⦆ Γ′
          txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ there

data _⨾_⨾_~ℍ[15]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₅-args}
    → let
        open H₁₅-args h

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ
            ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

        -- (iii) submit transaction T
        T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ v redeemable-by K̂ B′ ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
        open H₁₅ h (T at 0) using (λˢ)
      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[15]~ λᶜ ⨾ Rᶜ

-- ** Deposits: authorize destroy
record H₁₆-args : Type where
  constructor mk
  field
    {y Γ₀ t} : _
    {ds} : DepositRefs
    j : Index ds
    -- Hypotheses from [DEP-AuthDestroy]
    fresh-y : y ∉ ids Γ₀
  k  = length ds
  A  = (ds ‼ j) .proj₁
  xs = map (proj₂ ∘ proj₂) ds
  Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
  j′ = Index xs ∋ ‼-map {xs = ds} j
  open Transition
    ( (Δ ∣ Γ₀) ⨾ t
      —— auth-destroy⦅ A , xs , j′ ⦆ —→
      (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀) ⨾ t
    ⊣ Act ([DEP-AuthDestroy] fresh-y)
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₆ (⋯ : H₁₆-args) (let open H₁₆-args ⋯) where
  -- ** name resolution
  abstract
    xs↦ : xs ↦ TxInput′
    xs↦ = txout′ ∘ xs⊆
      where
      xs⊆ : xs ⊆ ids R
      xs⊆ = begin
        xs           ⊆⟨ namesʳ-∥map-authDestroy ds ⟩
        ids Δ        ⊆⟨ mapMaybe-⊆ isInj₂ $ ∈-collect-++⁺ˡ Δ Γ₀ ⟩
        ids Γ        ⊆⟨ ∈namesʳ-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ R≈) ⟩
        ids (R .end) ⊆⟨ namesʳ⦅end⦆⊆ R ⟩
        ids R        ∎ where open ⊆-Reasoning Secret
  --
  private
    names≡ : Γ′ ≡⦅ names ⦆ Γ
    names≡ rewrite collectFromBase-++ {X = Name} (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ]) Γ₀
                | collectFromBase-++ {X = Name} Δ (A auth[ xs , j′ ▷ᵈˢ y ])
                | L.++-identityʳ (names Δ)
                = sym $ collectFromBase-++ {X = Name} Δ Γ₀

    ids≡ :  Γ′ ≡⦅ ids ⦆ Γ
    ids≡ = cong filter₂ names≡

    secrets≡ : Γ′ ≡⦅ secrets ⦆ Γ
    secrets≡ = cong filter₁ names≡

    ads≡ : Γ′ ≡⦅ advertisements ⦆ Γ
    ads≡ rewrite collectFromBase-++ {X = Ad} (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ]) Γ₀
              | collectFromBase-++ {X = Ad} Δ (A auth[ xs , j′ ▷ᵈˢ y ])
              | L.++-identityʳ (advertisements Δ)
              = sym $ collectFromBase-++ {X = Ad} Δ Γ₀

    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ = lift Γ —⟨ ids ⟩— Γ′ ⊣ ids≡

    sechash↝ : Γ →⦅ Sechash ⦆ Γ′
    sechash↝  = lift Γ —⟨ secrets ⟩— Γ′ ⊣ secrets≡

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ = lift Γ —⟨ advertisements ⟩— Γ′ ⊣ ads≡
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝

data _⨾_⨾_~ℍ[16]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₆-args} {B}
    → let
        -- (ii) in Rˢ we find ⟨Bᵢ,vᵢ⟩yᵢ for i ∈ 1..k
        open H₁₆-args h

        -- (vii) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₆ h using (λˢ; xs↦)
      in
      -- (iii) in Rᶜ we find B → ∗ ∶ T
      --       for some T having txout′(yᵢ) as inputs (+ possibly others)
    ∀ (∃B : ∃ λ B → ∃ λ T  →
         (B →∗∶ encode (T .proj₂ .proj₂) ∈ toList Rᶜ)
       × ((hashTxⁱ <$> codom xs↦) ⊆ V.toList (∃inputs T)))
    → let
        -- (iv) broadcast transaction T, signed by A
        _ , T , B∈ , _ = ∃B
        m  = SIG (K̂ A) T
        λᶜ = B →∗∶ m
      in

      -- (v) λᶜ is the first broadcast of m in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m) (Any-front B∈)

    -- (vi) λᶜ does not correspond to any *other* symbolic move
    -- ∙ (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
    --   → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
    --   → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))

      ────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[16]~ λᶜ ⨾ Rᶜ

-- ** Deposits: destroy
record H₁₇-args : Type where
  constructor mk
  field
    {Γ₀ y t} : _
    {ds} : DepositRefs
    j : Index ds
  xs = map (proj₂ ∘ proj₂) ds
  Δ  = || flip map (enumerate ds) (λ{ (i , Aᵢ , vᵢ , xᵢ) →
          ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
  open Transition
    ( (Δ ∣ Γ₀) ⨾ t
      —— destroy⦅ xs ⦆ —→
      Γ₀ ⨾ t
    ⊣ Act [DEP-Destroy]
    ) public hiding (t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₇ (⋯ : H₁₇-args) (let open H₁₇-args ⋯) where
  -- ** name resolution
  abstract
    xs↦ : xs ↦ TxInput′
    xs↦ = txout′ ∘ xs⊆
      where
      xs⊆ : xs ⊆ ids R
      xs⊆ = begin
        xs           ⊆⟨ namesʳ-∥map-destroy ds ⟩
        ids Δ        ⊆⟨ mapMaybe-⊆ isInj₂ $ ∈-collect-++⁺ˡ Δ Γ₀ ⟩
        ids Γ        ⊆⟨ ∈namesʳ-resp-≈ _ {Γ}{cfg (R .end)} (↭-sym $ proj₂ R≈) ⟩
        ids (R .end) ⊆⟨ namesʳ⦅end⦆⊆ R ⟩
        ids R        ∎ where open ⊆-Reasoning Secret
  --
  private
    secrets≡ : secrets Γ ≡ secrets Δ ++ secrets Γ₀
    secrets≡ = mapMaybe∘collectFromBase-++ isInj₁ Δ Γ₀

    ids≡ : ids Γ ≡ ids Δ ++ ids Γ₀
    ids≡ = mapMaybe∘collectFromBase-++ isInj₂ Δ Γ₀

    txout↝ : Γ →⦅ Txout ⦆ Γ′
    txout↝ txout′ rewrite ids≡ = weaken-↦ txout′ (∈-++⁺ʳ _)

    sechash↝ : Γ →⦅ Sechash ⦆ Γ′
    sechash↝ sechash′ rewrite secrets≡ = weaken-↦ sechash′ (∈-++⁺ʳ _)

    κ↝ : Γ →⦅ 𝕂² ⦆ Γ′
    κ↝ κ′ = weaken-↦ κ′ (∈-collect-++⁺ʳ Δ Γ₀)

  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ txout↝ sechash↝ κ↝
  private
    𝕣′ : ℝ R′
    𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)
  abstract
    value-preserving⇒ :
      ValuePreservingʳ 𝕣
      ───────────────────
      ValuePreservingʳ 𝕣′
    value-preserving⇒ pv-txout = pv-txout′
      where
        open ≡-Reasoning

        txoutΓ : Txout Γ
        txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

        pv-txoutΓ : ValuePreserving {Γ} txoutΓ
        pv-txoutΓ =
          ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

        postulate pv↝ : ValuePreserving↝ {Γ}{Γ′} txout↝
        -- pv↝ txoutΓ pv-txoutΓ {x} x∈
        --   = ?

        txoutΓ′ : Txout Γ′
        txoutΓ′ = txout↝ txoutΓ

        pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
        pv-txoutΓ′ =  pv↝ txoutΓ pv-txoutΓ

        txoutΓ″ : Txout Γ″
        txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

        pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
        pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

        pv-txout′ : ValuePreservingʳ 𝕣′
        pv-txout′ x∈ =
          begin
            (𝕣′ ∙txoutEnd x∈) ∙value
          ≡⟨ cong _∙value
                $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
            (txoutΓ″ x∈) ∙value
          ≡⟨ pv-txoutΓ″ _ ⟩
            (Γ″ , x∈) ∙value
          ∎

data _⨾_⨾_~ℍ[17]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₇-args}
    → let
        -- (ii) in Rˢ, α assumes ⟨Aᵢ,vᵢ⟩xᵢ to obtain 0
        open H₁₇-args h

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        -- remove {⋯ xᵢ ↦ (Tᵢ,j) ⋯} from txout′
        open H₁₇ h using (λˢ; xs↦)
      in
    ∀ {i : ℕ}
      (T    : Tx i 0)
      (ins⊆ : (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T))
    → let
        -- (iii) submit transaction T
        λᶜ = submit (_ , _ , T)
      in

    -- (iv) λᶜ does not correspond to any *other* symbolic move
    -- ∙ (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
    --     → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
    --     → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))

      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[17]~ λᶜ ⨾ Rᶜ

-- ** After
record H₁₈-args : Type where
  constructor mk
  field
    {Γ t δ} : _
    δ>0 : δ > 0
  open Transition
    ( Γ ⨾ t —— delay⦅ δ ⦆ —→ Γ ⨾ (t + δ)
    ⊣ [Delay] δ>0
    ) public hiding (Γ; t)
  field 𝕙r : ℍ-Run Γ→
  open ℍ-Run 𝕙r public

module H₁₈ (⋯ : H₁₈-args) (let open H₁₈-args ⋯) where
  λˢ : ℾᵗ Γₜ′
  λˢ = LIFTˢ 𝕣 Γ R≈ Γ′ id id id
  private
    𝕣′ : ℝ R′
    𝕣′ = ℝ-step 𝕣 (𝕒 , λˢ)
  abstract
    value-preserving⇒ :
      ValuePreservingʳ 𝕣
      ───────────────────
      ValuePreservingʳ 𝕣′
    value-preserving⇒ pv-txout = pv-txout′
      where
        open ≡-Reasoning

        txoutΓ : Txout Γ
        txoutΓ = Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)

        pv-txoutΓ : ValuePreserving {Γ} txoutΓ
        pv-txoutΓ =
          ValuePreserving-Txout≈ {R ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_) pv-txout

        txoutΓ′ : Txout Γ′
        txoutΓ′ = txoutΓ

        pv-txoutΓ′ : ValuePreserving {Γ′} txoutΓ′
        pv-txoutΓ′ = pv-txoutΓ

        txoutΓ″ : Txout Γ″
        txoutΓ″ = Txout≈ {Γ′}{Γ″} (↭-sym Γ≈) txoutΓ′

        pv-txoutΓ″ : ValuePreserving {Γ″} txoutΓ″
        pv-txoutΓ″ = ValuePreserving-Txout≈ {Γ′} {Γ″} (↭-sym Γ≈) txoutΓ′ pv-txoutΓ′

        pv-txout′ : ValuePreservingʳ 𝕣′
        pv-txout′ x∈ =
          begin
            (𝕣′ ∙txoutEnd x∈) ∙value
          ≡⟨ cong _∙value
                $ txout∷∘namesʳ⦅end⦆⊆ {R = R} Γ→ (R≈′ , R≈) txoutΓ′ txout′ _ ⟩
            (txoutΓ″ x∈) ∙value
          ≡⟨ pv-txoutΓ″ _ ⟩
            (Γ″ , x∈) ∙value
          ∎

data _⨾_⨾_~ℍ[18]~_⨾_ : StepRel where
  mkℍ : ∀ {h : H₁₈-args}
    → let
        open H₁₈-args h
        open H₁₈ h using (λˢ)
        λᶜ = delay δ
      in
      ─────────────────────────────────────────────────────
      Γₜ″ ⨾ 𝕣∗ ⨾ (𝕒 , λˢ) ~ℍ[18]~ λᶜ ⨾ Rᶜ
