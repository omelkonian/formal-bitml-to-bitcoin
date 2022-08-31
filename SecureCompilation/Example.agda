{-# OPTIONS --no-forcing #-}
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

  -- instance
  --   Dec-Initial-Cfg : ∀ {Γ : Cfg} → Initial Γ ⁇
  --   Dec-Initial-Cfg {Γ} .dec = go Γ
  --     where
  --       go : ∀ Γ → Dec (Initial Γ)
  --       go ∅ᶜ                = yes tt
  --       go (⟨ _ has _ ⟩at _) = yes tt
  --       go (l ∣ r)           = Initial? l ×-dec Initial? r
  --       go (⟨ _ , _ ⟩at _)   = no λ ()
  --       go (l ∣ r)           = Initial? l ×-dec Initial? r
  --       go _                 = no {!λ ()!}

  --   Dec-Initial-Cfgᵗ : ∀ {Γₜ : Cfgᵗ} → Initial Γₜ ⁇
  --   Dec-Initial-Cfgᵗ {Γ at t} .dec = Initial? Γ ×-dec (t ≟ 0)

  infix 0 ∎_⊣_,_~_⊣_⊣_
  ∎_⊣_,_~_⊣_⊣_ :
    ∀ Γₜ₀ (init : Initial Γₜ₀) (ℽ₀ : ℾᵗ Γₜ₀) →
    ∀ (rᶜ : C.Run) (cinit : Initial rᶜ) →
    let open ℾᵗ ℽ₀; Γ₀ = Γₜ₀ .cfg in
    (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
        let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
        ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
              × (T₀ ‼ᵒ oᵢ ≡ v -redeemableWith- Kᵖʳⁱᵛ A))
    → (Γₜ₀ ∎⊣ init) ~ (rᶜ ∎⊣ cinit ✓)
  ∎ Γₜ ⊣ init , ℽ₀ ~ Rᶜ ⊣ cinit ⊣ txout≈ =
    -, base {ℽ = ℽ₀} init cinit txout≈

  infixl -1 _—→ᴸ_⊣_~_⊣_ _—→ᴿ_⊣_~_⊣_ _—→ᵋ_⊣_
  _—→ᴸ_⊣_~_⊣_ :
    ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
    ∀ Γₜ (λˢ : 𝕃 Rˢ Γₜ) λᶜ →
    (Γₜ ∷ Rˢ~Rᶜ .proj₁ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓) →
    (Γₜ ∷ Rˢ ⊣ λˢ .proj₁) ~ (λᶜ ∷ Rᶜ ✓)
  (𝕣∗ , coh) —→ᴸ Γₜ ⊣ λˢ ~ λᶜ ⊣ p =
    Γₜ ∷ 𝕣∗ ⊣ λˢ ✓ , step₁ {λˢ = λˢ} coh ([L] p)

  _—→ᴿ_⊣_~_⊣_ :
    ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
    ∀ Γₜ (λˢ : 𝕃 Rˢ Γₜ) λᶜ →
    (Γₜ ∷ Rˢ~Rᶜ .proj₁ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓) →
    (Γₜ ∷ Rˢ ⊣ λˢ .proj₁) ~ (λᶜ ∷ Rᶜ ✓)
  (𝕣∗ , coh) —→ᴿ Γₜ ⊣ λˢ ~ λᶜ ⊣ p =
    Γₜ ∷ 𝕣∗ ⊣ λˢ ✓ , step₁ coh ([R] p)

  _—→ᵋ_⊣_ :
    ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
    ∀ λᶜ →
    Rˢ~Rᶜ .proj₁ ~₂ Rᶜ ∷ʳ λᶜ →
    Rˢ ~ (λᶜ ∷ Rᶜ ✓)
  (𝕣∗ , coh) —→ᵋ λᶜ ⊣ p
    = 𝕣∗ , step₂ coh p

  Γ₀ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  Γₙ = ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N

  tc-run : S.Run
  tc-run = record {start = Γ₀ at0; init = auto; end = Γₙ at0; trace = -, tc-stepsₜ}

  postulate
    encodeStr : String → Message
    decodeStr : Message → Maybe String

  h : ℤ
  h = a ♯
  ℽ₀ : ℾᵗ (Γ₀ at0)
  ℽ₀ = [txout: (λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ) ∣sechash: (λ ()) ∣κ: (λ ()) ]

  rᶜ : C.Run
  rᶜ = submit (-, -, T₀)
      ∷ (A →∗∶ (Kᵖ A ∷ K̂ᵖ A ∷ []))
      ∷ (B →∗∶ (Kᵖ B ∷ K̂ᵖ B ∷ []))
      ∷ []

  cinit : Initial rᶜ
  cinit = -, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl

{-
  coh₀ : _ ~ _
  coh₀ =
    ∎ Γ₀ at0 ⊣ auto , ℽ₀
    ~ rᶜ     ⊣ cinit
    ⊣ λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl

  coh₁ : _ ~ _
  coh₁ =
    ∎ Γ₀ at0 ⊣ auto , ℽ₀
    ~ rᶜ     ⊣ cinit
    ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

    —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0 ⊣ ((advertise⦅ tc ⦆ , _) , _)
      ~ (A →∗∶ _)
      ⊣ [1] auto (_ , auto) auto auto (toWitness {Q = _ ⊆? _} tt)

  coh₁′ : _ ~ _
  coh₁′ =
    ∎ Γ₀ at0 ⊣ auto , ℽ₀
    ~ rᶜ     ⊣ cinit
    ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

    —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0 ⊣ ((advertise⦅ tc ⦆ , _) , _)
      ~ (A →∗∶ _)
      ⊣ [1] auto (_ , auto) auto auto (toWitness {Q = _ ⊆? _} tt)

    —→ᵋ (A →O∶ encodeStr a)
    ⊣ [2] (inj₁ refl)
-}
  coh₁″ : _ ~ _
  coh₁″ =
    ∎   Γ₀ at0 ⊣ auto , ℽ₀
      ~ rᶜ     ⊣ cinit
      ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

    —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0 ⊣ ((advertise⦅ tc ⦆ , _) , _)
      ~ (A →∗∶ _)
      ⊣ [1] {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y}
            auto (_ , auto) auto auto (toWitness {Q = _ ⊆? _} tt)

    —→ᵋ (A →O∶ encodeStr a)
      ⊣ [2] (inj₁ refl)

    —→ᵋ (O→ A ∶ [ h ])
      ⊣ [2] (inj₂ refl)

  coh₂ : _ ~ _
  coh₂ =
    ∎   Γ₀ at0 ⊣ auto , ℽ₀
      ~ rᶜ     ⊣ cinit
      ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

    —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0 ⊣ ((advertise⦅ tc ⦆ , _) , _)
      ~ (A →∗∶ _)
      ⊣ [1] {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y}
            auto (_ , auto) auto auto (toWitness {Q = _ ⊆? _} tt)

    —→ᵋ (A →O∶ encodeStr a)
      ⊣ [2] (inj₁ refl)

    —→ᵋ (O→ A ∶ [ h ])
      ⊣ [2] (inj₂ refl)

    —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]) at 0
        ⊣ ((auth-commit⦅ A , tc , [ a , just N ] ⦆ , _) , _)
      ~ (A →∗∶ _)
      ⊣ {!!}
      -- ⊣ [2] {k⃗ = K²} auto (_ , auto) auto auto auto
      --       {!!} ({!!} ∷ []) ((A , encodeStr a , 𝟘 , {!!}) ∷ [])
      --       auto (λ where (𝟘 , ()))

{-
  coh′ :
    (
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
            ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]} {v = 0}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
            ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
            ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                      ∣ A auth[ ♯▷ tc ]} {secrets = []}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    ⟨ Act {t = 0}
    $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y}
    ⟩←——
      Γ₀ at0
    ∎⊣ auto
    )
    ~
    ( (B →∗∶ _)
    ∷ (A →∗∶ _)
    ∷ (O→ A ∶ _)
    ∷ (A →O∶ _)
    ∷ (A →∗∶ _)
    ∷ ( submit (-, -, T₀)
      ∷ (A →∗∶ (Kᵖ A ∷ K̂ᵖ A ∷ []))
      ∷ (B →∗∶ (Kᵖ B ∷ K̂ᵖ B ∷ []))
      ∷ []
      ) ∎⊣ (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
    ✓ ✓ ✓ ✓ ✓ ✓
    )
  coh′ =
    -, (step₁
        (step₁
          (step₁
            (step₁
              (step₂
                (step₂
                  (base {ℽ = ℽ₀} auto (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
                    λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)
                  ([2] (inj₁ refl)))
                ([2] (inj₂ refl)))
              ([L] [2] {k⃗ = K²} auto (_ , auto) auto auto auto ?
                        (? ∷ []) ((A , encodeStr a , 𝟘 , {!!}) ∷ []) auto (λ where (𝟘 , ()))))
            ([L] [2] {k⃗ = K²} auto (_ , auto) auto auto auto ? [] [] auto λ ()))
          ([L] [3] auto (_ , auto) ? 𝟘 ?))
        ([L] [3] auto (_ , auto) ? auto ?))
-}

{-
  coh : ∃ (tc-run ~_)
  coh = -, -,
    step₁
      (step₁
        (step₁
          (step₁
            (step₁
              (step₁
                (step₁
                  (step₁
                    (step₂
                      (step₂
                        (base {ℽ = ℽ₀} auto cinit
                          λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)
                        ([2] (inj₁ refl)))
                      ([2] (inj₂ refl)))
                    ([L] [2] {k⃗ = K²} auto (_ , auto) auto auto auto ?
                             (? ∷ []) ((A , encodeStr a , 𝟘 , {!!}) ∷ []) auto (λ where (𝟘 , ()))))
                  ([L] [2] {k⃗ = K²} auto (_ , auto) auto auto auto ? [] [] auto λ ()))
                ([L] [3] auto (_ , auto) ? 𝟘 ?))
              ([L] [3] auto (_ , auto) ? auto ?))
            ([L] [4] auto (_ , auto) auto))
          ([L] [7] ? auto (_ , auto) (A , ?) ? ? ? ?))
        ([L] [6] refl refl auto (_ , auto) auto ? refl))
      ([L] [9] refl auto (_ , auto) auto refl [])
-}

{-
  --   (let open M₀ in
  --   ∎ Γₜ ⊣ auto , ℽ₀
  --   ~ Rᶜ ⊣ cinit
  --   ⊣ (λ where 𝟘 → 0F , {!!} , refl; 𝟙 → 1F , {!!}  , refl)
  --   )
  --   —→ᴸ M₁.Γₜ ⊣ M₁.λˢ
  --     ~ (A →∗∶ encode {M₀.Rˢ} M₁.txout′ tc)
  --     ⊣ [1] auto (M₁.Γ , auto) auto auto M₁.d⊆

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
-}

{-
  module M₀ where
    Γₜ = Γ₀ at0
    Rˢ = Γₜ ∎⊣ auto

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
    coh = -, base {ℽ = ℽ₀} auto cinit
      λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl
      where
        ℽ₀ : ℾᵗ Γₜ
        ℽ₀ = [txout: (λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ) ∣sechash: (λ ()) ∣κ: (λ ()) ]
    𝕣∗ = coh .proj₁

  module M₁ where
    open M₀ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = advertise⦅ tc ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    Γₜ = Γ at0
    Rˢ = Γₜ ⟨ Act {t = 0} $ C-Advertise {ad = tc} {Γ = Γ₀} ⟩←—— Rˢ′

    _C = encode {Rˢ′} txout′ tc
    λᶜ = A →∗∶ _C
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [1] auto (Γ , auto) auto auto d⊆)
      where
        d⊆ : tc ⊆⦅ deposits ⦆ Γ₀
        d⊆ = toWitness {Q = _ ⊆? _} tt
    𝕣∗ = coh .proj₁

  module M₁′ where
    open M₁ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    Rˢ = Rˢ′
    λᶜ = A →O∶ encodeStr a
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = let _ , coh₁ = coh′
          in -, step₂ coh₁ ([2] (inj₁ refl))
    𝕣∗ = coh .proj₁

  module M₁″ where
    open M₁′ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    Rˢ = Rˢ′
    λᶜ = O→ A ∶ [ h ]
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = let _ , coh₁ = M₁′.coh
          in -, step₂ coh₁ ([2] (inj₂ refl))
    𝕣∗ = coh .proj₁

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
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    _C = encode {Rˢ′} txout′ tc
    postulate C≡ : _C ≡ M₁._C

    h̅ : List ℤ
    h̅ = [ h ]

    k⃗ : 𝕂²′ tc
    k⃗ = K²

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)
    -- ≈ pub <$> [Kᵈ² A, Kᵈ² B, Kʷᵃ A, Kʷᵃ B, Kᵈ² A, Kᵈ² B]

    C,h̅,k̅ : Message
    C,h̅,k̅ = _C ◇ h̅ ◇ k̅

    λᶜ = A →∗∶ SIGᵐ (Kᵖᵘᵇ A) C,h̅,k̅
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂)
      ([L] [2] {k⃗ = k⃗} auto (_ , auto) auto auto auto ∃B h≡ h∈O auto h♯sechash)
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite C≡ = A , 𝟚

        h≡ : All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅
        h≡ = {!!} ∷ []

        h∈O : CheckOracleInteractions Rᶜ′ _
        h∈O = (A , encodeStr a , 𝟘 , {!!}) ∷ []

        h♯sechash : Disjoint h̅ (codom sechash′)
        h♯sechash (𝟘 , ())
    𝕣∗ = coh .proj₁

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
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    _C = encode {Rˢ′} txout′ tc
    postulate C≡ : _C ≡ M₂._C

    h̅ : List ℤ
    h̅ = []

    k⃗ : 𝕂²′ tc
    k⃗ = K²

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ : Message
    C,h̅,k̅ = _C ◇ h̅ ◇ k̅

    λᶜ = B →∗∶ SIGᵐ (Kᵖᵘᵇ B) C,h̅,k̅
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂)
      ([L] [2] {k⃗ = k⃗} auto (_ , auto) auto auto auto ∃B [] [] auto λ ())
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite trans C≡ M₂.C≡ = A , 𝟛
    𝕣∗ = coh .proj₁

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
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants tc
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
        ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 tc (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
                       A x auto Γ→ (Γ , auto) committedA
      public using (T; λˢ)

    λᶜ = A →∗∶ [ SIG (Kᵖʳⁱᵛ A) T ]
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA 𝟘 ∃B)
      where
        ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
        ∃B = {!!}
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
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants tc
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
        ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 tc (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ])
                       B y auto Γ→ (Γ , auto) committedA
      public using (T)

    λᶜ = B →∗∶ [ SIG (Kᵖʳⁱᵛ B) T ]
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA auto ∃B)
      where
        ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
        ∃B = {!!}
    𝕣∗ = coh .proj₁
-}

{-
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
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    toSpend = persistentDeposits (tc .G)

    open H₄ 𝕣 0 α 0 tc (⟨ A ∶ a ♯ just 9 ⟩) toSpend 1 x₁ auto Γ→ (Γ , auto)
      public using (T)

    λᶜ = submit T
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [4] auto (Γ , auto) auto)
    𝕣∗ = coh .proj₁
-}

{-
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

    λᶜ = A →∗∶ encodeStr a
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [7] ? auto (Γ , auto) (A , ?) ? ? ? ?)
    -- coh = -, step₁ (coh′ .proj₂) ([L] [7] ? auto (Γ , auto) (A , 𝟘) 𝟜 𝟘 ? ?)
    𝕣∗ = coh .proj₁
-}
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
    coh = -, step₁ (coh′ .proj₂) ([L] [6] refl refl auto (Γ , auto) auto ? refl)

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
    coh = -, step₁ (coh′ .proj₂) ([L] [9] refl auto (Γ , auto) auto refl [])

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁
-}
