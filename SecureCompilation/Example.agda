----------------------------------------------------------------------------
-- Example contract compilations.
----------------------------------------------------------------------------
module SecureCompilation.Example where

open import Prelude.Init hiding (T)
open L.Mem
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Prelude.Validity
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Functor
open import Prelude.Collections
open import Prelude.Membership hiding (_∈_; _∉_; mapWith∈)
open import Prelude.ToList
open import Prelude.Traces

-- Bitcoin
module BTC where
  open import Bitcoin public
    using (_`=_; _`<_; _`∧_; `; `true; ∣_∣)
open import Bitcoin
  hiding ( t
         ; _`=_; _`<_; _`∧_; `; `true; ∣_∣
         )

-- BitML
open import BitML.Example.Setup using (Participant; Honest; A; B)
module BML where
  open import BitML Participant Honest public
    using (⟦_⟧_; _`=_; _`∧_; `_; `true; _`<_; _∣_)
open import BitML Participant Honest
  hiding ( t; a; v; A; B; x; y; Γ₀; Γₜ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′
         ; ∣_∣; `
         ; ⟦_⟧_; _`=_; _`∧_; `_; `true; _`<_; _∣_
         )
open Induction using (CS)

-- BitML compiler
η = 1
open import SecureCompilation.Compiler Participant Honest η

-- [TODO] move to `formal-bitcoin`
tx↝ : TxInput′ → TxInput
tx↝ record {tx′ = tx; index′ = i} = record {txId = tx ♯; index = toℕ i}

module Section7 where -- (see BitML paper, Section 7).

  ex-ad : Advertisement
  ex-ad = ⟨ A :! 1 at "x" ∣∣ B :! 1 at "y" ⟩ withdraw B ∙

  partG = nub-participants (ex-ad .G)

  postulate
    Tˣ Tʸ : TxInput′ -- pre-existing deposits

  sechash : namesˡ (ex-ad .G) ↦ ℤ
  sechash ()

  txout : namesʳ (ex-ad .G) ↦ TxInput′
  txout = case_of λ where
    {- "x" -} (here _)         → Tˣ
    {- "y" -} (there (here _)) → Tʸ

  postulate
    Kᵃ Kᵇ : KeyPair
    Kʷᵇ : Participant → KeyPair

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} (here _)         → Kᵃ
    {- B -} (there (here _)) → Kᵇ

  K² : subterms′ (CS $ ex-ad .C) ↦ (partG ↦ KeyPair)
  K² = case_of λ where
    (here _) → case_of λ where
      {- A -} (here _)         → Kʷᵇ A
      {- B -} (there (here _)) → Kʷᵇ B

  Ks : List KeyPair
  Ks = mapWith∈ partG (K² $ here refl)

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs  = tx↝ <$> Tˣ ∷ Tʸ ∷ []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 2 , record { value = 2; validator = ƛ versig Ks (allFin _) }]
    ; absLock = 0 }

  Tᵇ : Tx 1 1
  Tᵇ = sig⋆ V.[ Ks ] record
    { inputs  = V.[ (Tᵢₙᵢₜ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 1 , record { value = 2; validator = ƛ versig [ K (there (here refl)) ] [ 0F ] }]
    ; absLock = 0 }

  -- out : ∃Tx × (subterms⁺ (CS $ ex-ad .C) ↦ ∃Tx)
  -- out = bitml-compiler {ad = ex-ad} auto sechash txout K K²

--   outTxs : List ∃Tx
--   outTxs = let t₀ , m = out in t₀ ∷ m (here refl) ∷ []

--   _ : outTxs ≡ (-, -, Tᵢₙᵢₜ) ∷ (-, -, Tᵇ) ∷ []
--   _ = refl

module TimedCommitment where -- (see BitML, Appendix A.5)

  open import BitML.Example.TimedCommitment

  -- t = 42 ;
  v = 1 ; Ha = + 9

  partG = nub-participants (tc .G)

  postulate
    Kᵃ Kᵇ K̂ᵃ K̂ᵇ : KeyPair
    Kᵈ¹ Kᵈ² Kʷᵃ : Participant → KeyPair

  T₀ : Tx 0 2
  T₀ = record
    { inputs  = []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs =
        (Ctx 1 , record {value = 1 ; validator = ƛ (versig [ K̂ᵃ ] [ # 0 ])})
      ∷ (Ctx 1 , record {value = 0 ; validator = ƛ (versig [ K̂ᵇ ] [ # 0 ])})
      ∷ []
    ; absLock = 0 }

  -- pre-existing deposits
  Tᵃ Tᵇ : TxInput′
  Tᵃ = (-, -, T₀) at 0F
  Tᵇ = (-, -, T₀) at 1F

  pattern 𝟘 = here refl
  pattern 𝟙 = there 𝟘
  pattern 𝟚 = there 𝟙
  pattern 𝟛 = there 𝟚
  pattern 𝟜 = there 𝟛
  pattern 𝟝 = there 𝟜
  pattern 𝟞 = there 𝟝
  pattern 𝟟 = there 𝟞
  pattern 𝟠 = there 𝟟
  pattern 𝟡 = there 𝟠

  pattern 𝟘⊥ = here ()
  pattern 𝟙⊥ = there (here ())
  pattern 𝟚⊥ = there (there (here ()))

  sechash : namesˡ (tc .G) ↦ ℤ
  sechash = case_of λ where
    {- "a" -} 𝟘 → Ha

  txout : namesʳ (tc .G) ↦ TxInput′
  txout = case_of λ where
    {- "x" -} 𝟘 → Tᵃ
    {- "y" -} 𝟙 → Tᵇ

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} 𝟘 → Kᵃ
    {- B -} 𝟙 → Kᵇ

  K² : subterms′ (CS $ tc .C) ↦ (partG ↦ KeyPair)
  K² = case_of λ where
    {- reveal "a" ⇒ withdraw A -}
    𝟘 → case_of λ where
      {- A -} 𝟘 → Kᵈ² A
      {- B -} 𝟙 → Kᵈ² B
    {- withdraw A -}
    𝟙 → case_of λ where
      {- A -} 𝟘 → Kʷᵃ A
      {- B -} 𝟙 → Kʷᵃ B
    {- after t ⇒ withdraw B -}
    𝟚 → case_of λ where
      {- A -} 𝟘 → Kᵈ² A
      {- B -} 𝟙 → Kᵈ² B

  K⋆ : subterms′ (CS $ tc .C) ↦ List KeyPair
  K⋆ = mapWith∈ partG ∘ K²

  module _ where
    open BTC

    e₁ : Script (Ctx 3) `Bool
    e₁ = versig (K⋆ 𝟘) ⟦ # 0 , # 1 ⟧
      `∧ `true
      `∧ ⋀ [ hash (var (# 2)) `= ` (sechash 𝟘) `∧ (` (+ η) `< ∣ var (# 2) ∣) ]

    e₂ : Script (Ctx 3) `Bool
    e₂ = versig (K⋆ 𝟚) ⟦ # 0 , # 1 ⟧

    e′ : Script (Ctx 2) `Bool
    e′ = versig (K⋆ 𝟙) ⟦ # 0 , # 1 ⟧

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs  = tx↝ <$> Tᵃ ∷ Tᵇ ∷ []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ _ , record { value = v ; validator = ƛ (e₁ `∨ e₂) }]
    ; absLock = 0 }
  Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

  T′ : Tx 1 1
  T′ = sig⋆ V.[ K⋆ 𝟘 ] record
    { inputs  = V.[ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ _ , record { value = v ; validator = ƛ e′ }]
    ; absLock = 0 }

  T′ᵃ : Tx 1 1
  T′ᵃ = sig⋆ V.[ K⋆ 𝟙 ] record
    { inputs  = V.[ ((∃Tx ∋ -, -, T′) ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ versig [ K 𝟘 ] [ # 0 ] }]
    ; absLock = 0 }

  T′ᵇ : Tx 1 1
  T′ᵇ = sig⋆ V.[ K⋆ 𝟚 ] record
    { inputs  = V.[ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ versig [ K 𝟙 ] [ # 0 ] }]
    ; absLock = t }

  out : ∃Tx¹ × (subtermsᵃ⁺ tc ↦′ ∃Txᶜ)
  out = bitml-compiler {ad = tc} auto sechash txout K K²

  outTxs : Tx 2 1 × Tx 1 1 × Tx 1 1 × Tx 1 1
  outTxs = let t₀ , m = out in
      t₀ .proj₂
    , m 𝟘 .proj₂
    , m 𝟙 .proj₂
    , m 𝟚 .proj₂

  _ = outTxs ≡ (Tᵢₙᵢₜ , T′ , T′ᵃ , T′ᵇ)
    ∋ refl


  open import SymbolicModel.Run.Base Participant Honest as S
    hiding (Rˢ; Rˢ′)
  open import SymbolicModel.Helpers Participant Honest
  open import SymbolicModel.Mappings Participant Honest

  finPart : Finite Participant
  finPart = 2 , Fun.mk↔
    {f   = λ where A → 0F; B → 1F}
    {f⁻¹ = λ where 0F → A; 1F → B}
    ((λ where 0F → refl; 1F → refl) , (λ where A → refl; B → refl))

  keypairs : Participant → KeyPair × KeyPair
  keypairs A = Kᵃ , K̂ᵃ
  keypairs B = Kᵇ , K̂ᵇ

  open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
    hiding (Rᶜ; Rᶜ′; λᶜ; m)
  open import ComputationalModel.KeyPairs Participant keypairs
    renaming (K̂ to Kᵖʳⁱᵛ; K to Kᵖᵘᵇ)
  open import SecureCompilation.Helpers   Participant Honest finPart keypairs η
  open import SecureCompilation.Coherence Participant Honest finPart keypairs η

  infix 0 _at0
  _at0 : Cfg → Cfgᵗ
  _at0 = _at 0

  open BML

  infix 0 ∎_⊣_,_~_⊣_⊣_
  ∎_⊣_,_~_⊣_⊣_ :
    ∀ Γₜ₀ (init : Initial Γₜ₀) (ℽ₀ : ℾᵗ Γₜ₀) →
    ∀ Rᶜ (cinit : Initial Rᶜ) →
    let open ℾᵗ ℽ₀; Γ₀ = Γₜ₀ .cfg in
    (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
        let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
        ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
              × (T₀ ‼ᵒ oᵢ ≡ v -redeemableWith- Kᵖʳⁱᵛ A))
    → (Γₜ₀ ∎⊣ init) ~ Rᶜ
  ∎  Γₜ ⊣ init , ℽ₀
    ~ Rᶜ ⊣ cinit
    ⊣ txout≈
    = ℽ₀ ∎⊣ init ✓
    , base init cinit txout≈

  infixl -1 _—→ᴸ_⊣_~_⊣_
  _—→ᴸ_⊣_~_⊣_ :
    ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
    ∀ Γₜ (λˢ : 𝕃 Rˢ Γₜ) λᶜ →
    (Γₜ ∷ Rˢ~Rᶜ .proj₁ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓) →
    (Γₜ ∷ Rˢ ⊣ λˢ .proj₁) ~ (λᶜ ∷ Rᶜ ✓)
  (𝕣∗ , coh)
    —→ᴸ Γₜ ⊣ λˢ
      ~ λᶜ
      ⊣ p
    = Γₜ ∷ 𝕣∗ ⊣ λˢ ✓
    , step₁ coh ([L] p)

  Γ₀  = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y

  -- coh : M₁.Rˢ ~ M₁.Rᶜ
  -- coh =
  --   (let open M₀ in
  --   ∎ Γₜ ⊣ auto , ℽ₀
  --   ~ Rᶜ ⊣ cinit
  --   ⊣ (λ where 𝟘 → 0F , {!!} , refl; 𝟙 → 1F , {!!}  , refl)
  --   )
  --   —→ᴸ M₁.Γₜ ⊣ M₁.λˢ
  --     ~ (A →∗∶ encode {M₀.Rˢ} M₁.txout′ tc)
  --     ⊣ [1] auto (M₁.Γ , auto) auto auto M₁.d⊆

  -- postulate
  --   encodeAd : Ad → Message

  -- ℂ : Message
  -- ℂ = encodeAd tc

  -- coh : (
  --         ((` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at0)
  --       ⟨ Act {t = 0} $ C-Advertise {ad = tc} {Γ = Γ₀} ⟩←——
  --         (((⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at0) ∎⊣ auto)
  --       )
  --     ~ ( (A →∗∶ {!!}) -- encodeAd)
  --       ∷ ( submit (-, -, T₀)
  --         ∷ (A →∗∶ (Kᵖ A ∷ K̂ᵖ A ∷ []))
  --         ∷ (B →∗∶ (Kᵖ B ∷ K̂ᵖ B ∷ []))
  --         ∷ []) ∎⊣ (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
  --       ✓ ✓
  --       )
  -- coh = -, step₁
  --   (base auto
  --      (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
  --      (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl))
  --   ([L] [1] auto (_ , auto) auto auto d⊆)
  --   where
  --     d⊆ : tc ⊆⦅ deposits ⦆ Γ₀
  --     d⊆ = toWitness {Q = _ ⊆? _} tt

  module M₀ where
    Γₜ = Γ₀ at0
    Rˢ = Γₜ ∎⊣ auto

    ℽ₀ : ℾᵗ Γₜ
    ℽ₀ = [txout: (λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ) ∣sechash: (λ ()) ∣κ: (λ ()) ]

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = _∎⊣_✓ {Γₜ = Γₜ} ℽ₀ auto

    rᶜ : C.Run
    rᶜ = submit (-, -, T₀)
       ∷ (A →∗∶ (Kᵖ A ∷ K̂ᵖ A ∷ []))
       ∷ (B →∗∶ (Kᵖ B ∷ K̂ᵖ B ∷ []))
       ∷ []

    cinit : Initial rᶜ
    cinit = -, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl

    Rᶜ : CRun
    Rᶜ = rᶜ ∎⊣ cinit ✓

    coh : Rˢ ~ Rᶜ
    coh = 𝕣∗ , base auto cinit λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl
    -- coh =
    --   ∎ Γ₀ at0 ⊣ auto , ℽ₀
    --   ~ Rᶜ ⊣ cinit
    --   ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

  module M₁ where
    open M₀ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = advertise⦅ tc ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0} $ C-Advertise {ad = tc} {Γ = Γ₀}

    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    open H₁ 𝕣 0 α 0 Γ₀ auto tc Γ→ (Γ , auto) public using (λˢ)

    _C : Message
    _C = encode {Rˢ′} txout′ tc

    λᶜ = A →∗∶ _C

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = Γₜ ∷ 𝕣∗′ ⊣ λˢ ✓

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    -- d⊆ : tc ⊆⦅ deposits ⦆ Γ₀
    -- d⊆ = toWitness {Q = _ ⊆? _} tt

    coh : Rˢ ~ Rᶜ
    coh = 𝕣∗ , step₁ (coh′ .proj₂) ([L] [1] auto (Γ , auto) auto auto d⊆)
      where
        d⊆ : tc ⊆⦅ deposits ⦆ Γ₀
        d⊆ = toWitness {Q = _ ⊆? _} tt
    -- coh =
    --     M₀.coh
    --   —→ᴸ Γₜ ⊣ λˢ
    --     ~ (A →∗∶ encode {M₀.Rˢ} txout′ tc)
    --     ⊣ [1] auto (Γ , auto) auto auto d⊆

  h : ℤ
  h = a ♯

  postulate
    encodeStr : String → Message
    decodeStr : Message → Maybe String

  module M₁′ where
    open M₁ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    λᶜ = A →O∶ encodeStr a
    Rᶜ = λᶜ ∷ Rᶜ′ ✓
    Rˢ = Rˢ′
    𝕣∗ = 𝕣∗′

    coh : Rˢ ~ Rᶜ
    coh = let 𝕣∗ , coh₁ = coh′
          in  𝕣∗ , step₂ coh₁ ([2] (inj₁ refl))

  module M₁″ where
    open M₁′ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    λᶜ = O→ A ∶ [ h ]
    Rᶜ = λᶜ ∷ Rᶜ′ ✓
    Rˢ = Rˢ′
    𝕣∗ = 𝕣∗′

    coh : Rˢ ~ Rᶜ
    coh = let 𝕣∗ , coh₁ = M₁′.coh
          in  𝕣∗ , step₂ coh₁ ([2] (inj₂ refl))

  module M₂ where
    open M₁″ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-commit⦅ A , tc , [ a , just N ] ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    Δ×h̅ : List (Secret × Maybe ℕ × ℤ)
    Δ×h̅ = [ a , just N , h ]

    Δ : List (Secret × Maybe ℕ)
    Δ = map drop₃ Δ×h̅

    as : List Secret
    as = unzip Δ .proj₁

    sechash⁺ : as ↦ ℤ
    -- sechash⁺ = λ where
    --   {- a -} 𝟘 → h
    sechash⁺ {a} a∈ =
      let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
          (_ , _ , z) , _ = ∈-map⁻ drop₃ a×m∈
      in z

    k⃗ : 𝕂²′ tc
    k⃗ = K²

    open H₂ 𝕣 0 α 0 _ auto A A tc Δ sechash⁺ k⃗ Γ→ (Γ , auto) public using (λˢ)

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = Γₜ ∷ 𝕣∗′ ⊣ λˢ ✓

    _C : Message
    _C = encode {Rˢ′} txout′ tc

    postulate C≡ : _C ≡ M₁._C

    h̅ : List ℤ
    h̅ = map (proj₂ ∘ proj₂) Δ×h̅ -- [ a ]

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ : Message
    C,h̅,k̅ = _C ◇ h̅ ◇ k̅

    λᶜ : C.Label
    λᶜ = A →∗∶ SIGᵐ (Kᵖᵘᵇ A) C,h̅,k̅

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = 𝕣∗ , step₁ (coh′ .proj₂) ([L] [2] auto (_ , auto) auto auto auto ∃B h≡ h∈O auto h♯sechash)
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite C≡ = A , 𝟚

        h≡ : All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅
        h≡ = {!!} ∷ []

        h∈O : CheckOracleInteractions Rᶜ′ Δ×h̅
        h∈O = {!!}

        h♯sechash : Disjoint h̅ (codom sechash′)
        h♯sechash (𝟘 , ())

  module M₃ where
    open M₂ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-commit⦅ B , tc , [] ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]}
                      {secrets = []}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    Δ×h̅ : List (Secret × Maybe ℕ × ℤ)
    Δ×h̅ = []

    Δ : List (Secret × Maybe ℕ)
    Δ = map drop₃ Δ×h̅

    as : List Secret
    as = unzip Δ .proj₁

    sechash⁺ : as ↦ ℤ
    -- sechash⁺ ()
    sechash⁺ {a} a∈ =
      let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
          (_ , _ , z) , _ = ∈-map⁻ drop₃ a×m∈
      in z

    k⃗ : 𝕂²′ tc
    k⃗ = K²

    open H₂ 𝕣 0 α 0 _ auto B B tc Δ sechash⁺ k⃗ Γ→ (Γ , auto) public using (λˢ)

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = Γₜ ∷ 𝕣∗′ ⊣ λˢ ✓

    _C : Message
    _C = encode {Rˢ′} txout′ tc

    postulate C≡ : _C ≡ M₂._C

    h̅ : List ℤ
    h̅ = map (proj₂ ∘ proj₂) Δ×h̅ -- []

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ : Message
    C,h̅,k̅ = _C ◇ h̅ ◇ k̅

    λᶜ : C.Label
    λᶜ = B →∗∶ SIGᵐ (Kᵖᵘᵇ B) C,h̅,k̅

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = 𝕣∗ , step₁ (coh′ .proj₂) ([L] [2] auto (_ , auto) auto auto auto ∃B h≡ h∈O auto h♯sechash)
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite trans C≡ M₂.C≡ = A , 𝟛

        h≡ : All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅
        h≡ = []

        h∈O : CheckOracleInteractions Rᶜ′ Δ×h̅
        h∈O = []

        h♯sechash : Disjoint h̅ (codom sechash′)
        h♯sechash = λ ()

  module M₄ where
    open M₃ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-init⦅ A , tc , x ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
              ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants tc
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
        ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 tc (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
                       A x auto Γ→ (Γ , auto) committedA
      public using (T)

    λᶜ : C.Label
    λᶜ = A →∗∶ [ SIG (Kᵖʳⁱᵛ A) T ]

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] {![3] ? ? ? ? ?!})
    -- coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA auto ∃B)
    --   where
    --     ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
    --     ∃B = ?

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

  module M₅ where
    open M₄ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-init⦅ B , tc , y ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
              ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]} {v = 0}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants tc
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
        ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 tc (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ])
                       B y auto Γ→ (Γ , auto) committedA
      public using (T)

    λᶜ : C.Label
    λᶜ = A →∗∶ [ SIG (Kᵖʳⁱᵛ B) T ]

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] {![3] ? ? ? ? ?!})
    -- coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA auto ∃B)
    --   where
    --     ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
    --     ∃B = ?

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

  module M₆ where
    open M₅ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = init⦅ tc .G , tc .C ⦆
    Γ  = ⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    toSpend = persistentDeposits (tc .G)

    open H₄ 𝕣 0 α 0 tc (⟨ A ∶ a ♯ just 9 ⟩) toSpend 1 x₁ auto Γ→ (Γ , auto)
      public using (T)

    λᶜ : C.Label
    λᶜ = submit T

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) {!!} -- ([L] [4] auto (Γ , auto) fresh-x₁)
      where
        fresh-x₁ : x₁ ∉ (x ∷ y ∷ [])
        fresh-x₁ = λ where 𝟘⊥; 𝟙⊥

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

  module M₇ where
    open M₆ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-rev⦅ A , a ⦆
    Γ  = ⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ [C-AuthRev] {n = 9} {Γ = ⟨ tc .C , 1 ⟩at x₁}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = A →∗∶ encodeStr a

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ? -- ([L] [7] ? auto (Γ , auto) (A , 𝟘) 𝟜 𝟘 ? ?)

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

{-
  module M₈ where
    open M₇ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = put⦅ [] , [ a ] , x₁ ⦆
    Γ  = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Timeout {c = tc .C} {t = 0} {v = 1} {i = 0F}
       $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = submit T′

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [6] refl refl auto (Γ , auto) fresh-x₂ ? refl)
      where
        fresh-x₂ : x₂ ∉ [ x₁ ]
        fresh-x₂ 𝟘⊥

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

  module M₉ where
    open M₈ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = withdraw⦅ A , 1 , x₂ ⦆
    Γ  = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Timeout {c = [ withdraw A ]} {t = 0} {v = 1} {i = 0F}
       $ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = submit T′ᵃ

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [9] refl auto (Γ , auto) fresh-x₃ refl [])
      where
        fresh-x₃ : x₃ ∉ [ x₂ ]
        fresh-x₃ 𝟘⊥

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁
-}

  tc-run : S.Run
  tc-run = record
    { start = (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    ; init  = auto
    ; end   = (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
    ; trace = -, tc-stepsₜ
    }

  -- coh : ∃ (tc-run ~_)
    -- tc-run ~
    --  ( submit (-, -, T′ᵃ)
    --  ∷ submit T′
    --  ∷ B →∗∶ _
    --  ∷ A →∗∶ _
    --  ∷ A →∗∶ _
    --  ∷ submit (-, -, Tᵢₙᵢₜ)
    --  ∷ B →∗∶ _
    --  ∷ A →∗∶ _
    --  ∷ A →∗∶ _
    --  ∷ ( submit (-, -, T₀)
    --    ∷ (A →∗∶ (Kᵖ A ∷ K̂ᵖ A ∷ []))
    --    ∷ (B →∗∶ (Kᵖ B ∷ K̂ᵖ B ∷ []))
    --    ∷ []
    --    ) ∎⊣ (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
    --  ✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓ ✓)
  -- coh = -, M₉.coh

{-
  ⋮
  --- Initial configuration ---
  ∙ Tᵃ : TxInput′ {v = 1; sig = A}
  ∙ Tᵇ : TxInput′ {v = 0; sig = B}
  ⋮
  -- advertise⦅ tc ⦆
  A →∗∶ ♯tc♯
  -- auth-commit⦅ A , tc , [ a , just N ] ⦆
  A →∗∶ (♯tc♯ ◇ ♯[h]♯ ◇ ♯[k]♯)ᵃ
  -- auth-commit⦅ B , tc , [] ⦆
  B →∗∶ (♯tc♯ ◇ ♯[]♯ ◇ ♯[]♯)ᵇ
  -- auth-init⦅ A , tc , x ⦆
  A →∗∶ (Tᵢₙᵢₜ ♯)ᵃ
  -- auth-init⦅ B , tc , y ⦆
  B →∗∶ (Tᵢₙᵢₜ ♯)ᵇ
  -- init⦅ G tc , tc .C ⦆
  submit Tᵢₙᵢₜ
  -- auth-rev⦅ A , a ⦆
  A →∗∶ ♯tc♯ ◇ [h] ◇ [k]
  -- put⦅ [] , [ a ] , x₁ ⦆
  submit T′
  -- withdraw⦅ A , 1 , x₂ ⦆
  submit T′ᵃ
-}

{- Coherence DSL

tc-steps-coh :
  Rᶜ₀ ≈
  (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    —[ advertise⦅ tc ⦆                        ~ (A →∗∶ encode tc)
     ∷ ε                                      ~ (A →O∶ a)
     ∷ ε                                      ~ (O →A∶ h)
     ∷ auth-commit⦅ A , tc , [ a , just N ] ⦆ ~ (A →∗∶ C,h,k̅)
     ∷ auth-commit⦅ B , tc , [] ⦆             ~ (B →∗∶ C,h,k̅)
     ∷ auth-init⦅ A , tc , x ⦆                ~ (A →∗∶ SIG Kᴬ Tᵢₙᵢₜ)
     ∷ auth-init⦅ B , tc , y ⦆                ~ (B →∗∶ SIG Kᴬ Tᵢₙᵢₜ)
     ∷ init⦅ G tc , tc .C ⦆                   ~ submit Tᵢₙᵢₜ
     ∷ auth-rev⦅ A , a ⦆                      ~ (A →∗∶ a)
     ∷ put⦅ [] , [ a ] , x₁ ⦆                 ~ submit T′
     ∷ withdraw⦅ A , 1 , x₂ ⦆                 ~ submit T′ₐ
     ∷ []
     ]↠ₜ
  (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
tc-steps-coh =
  begin
    (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    ≈ Rᶜ₀@(A →∗∶ K.. ∷ A →∗∶ K.. ∷ submit T₀)
    ⊣ base cinit auto ... init ...
  —→⟨ Act {t = 0}
    $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y}
    ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    ↝ (A →∗∶ encode {...} txout′ tc)
    ⊣ [L] [1] ....
  —→ᵋ (A →O∶ a)
    ⊣ step₂ [2] ...
  —→ᵋ (O→ A ∶ h)
    ⊣ step₂ [2] ...
  —→⟨ Act {t = 0}
    $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]}
    ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
          ∣ A auth[ ♯▷ tc ]) at 0
    ↝ (A →∗∶ SIG Kᴬ C,h̅,k̅)
    ⊣ [L] [2] ...
  —→⟨ Act {t = 0}
    $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9
    ⟩
                       ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
          ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]) at 0
    ↝ (B →∗∶ SIG Kᴮ C,h̅,k̅)
    ⊣ [L] [2] ...
  —→⟨ Act {t = 0}
    $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9
    ⟩
                     ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
          ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]) at 0
    ↝ (A →∗∶ SIG Kᴬ Tᵢₙᵢₜ)
    ⊣ [L] [3] ...
  —→⟨ Act {t = 0}
    $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9
    ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                  {v = 0} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
          ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]) at 0
    ↝ (B →∗∶ SIG Kᴮ Tᵢₙᵢₜ)
    ⊣ [L] [3] ...
  —→⟨ Act {t = 0}
    $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩}
    ⟩
    (⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩) at 0
    ↝ submit Tᵢₙᵢₜ
    ⊣ [L] [4] ...
  —→⟨ Act {t = 0}
    $ [C-AuthRev] {n = 9} {Γ = ⟨ tc .C , 1 ⟩at x₁}
    ⟩
    (⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9) at 0
    ↝ (A →∗∶ a)
    ⊣ [L] [7] ...
  —→⟨ Timeout {c = tc .C} {t = 0} {v = 1} {i = 0F}
    $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]}
    ⟩
    (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9) at 0
    ↝ submit T′
    ⊣ [L] [6] ...
  —→⟨ Timeout {c = [ withdraw A ]} {t = 0} {v = 1} {i = 0F}
    $ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9}
    ⟩
    (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
    ↝ submit T′ᵃ
    ⊣ [L] [9] ...
  ∎

-}
