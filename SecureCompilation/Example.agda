----------------------------------------------------------------------------
-- Example contract compilations.
----------------------------------------------------------------------------
module SecureCompilation.Example where

open import Prelude.Init
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Prelude.Lists

-- Bitcoin
open import Bitcoin.Crypto using (KeyPair; HASH)
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto using (sig⋆; hashTx; wit⊥)

-- BitML
open import BitML.Example.Setup       using (Participant; Honest; A; B)
open import BitML.BasicTypes          hiding (t; a; v)
open import BitML.Contracts.Types     Participant Honest hiding (A; B)
open import BitML.Contracts.Induction Participant Honest using (CS)
open import BitML.Contracts.Helpers   Participant Honest
open import BitML.Contracts.Validity  Participant Honest using (ValidAdvertisement; validAd?)

-- BitML compiler
η = 1
open import SecureCompilation.Compiler Participant Honest η

module Section7 where -- (see BitML paper, Section 7).

  ex-ad : Advertisement
  ex-ad = ⟨ A :! 1 at "x" ∣∣ B :! 1 at "y" ⟩ withdraw B ∙

  partG = nub-participants (ex-ad .G)

  postulate
    Tˣ Tʸ : TxInput -- pre-existing deposits

  valid : ValidAdvertisement ex-ad
  valid = toWitness {Q = validAd? ex-ad} tt

  sechash : namesˡ (ex-ad .G) ↦ ℤ
  sechash ()

  txout : namesʳ (ex-ad .G) ↦ TxInput
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
    { inputs  = Tˣ ∷ Tʸ ∷ []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 2 , record { value = 2; validator = ƛ versig Ks (allFin _) }]
    ; absLock = 0 }

  Tᵇ : Tx 1 1
  Tᵇ = sig⋆ V.[ Ks ] record
    { inputs  = V.[ hashTx (-, -, Tᵢₙᵢₜ) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 1 , record { value = 2; validator = ƛ versig [ K (there (here refl)) ] [ 0F ] }]
    ; absLock = 0 }

  out : ∃Tx × (subterms⁺ (CS $ ex-ad .C) ↦ ∃Tx)
  out = bitml-compiler {g = ex-ad .G} {ds = ex-ad .C} valid sechash txout K K²

  outTxs : List ∃Tx
  outTxs = let t₀ , m = out in t₀ ∷ m (here refl) ∷ []

  _ : outTxs ≡ (-, -, Tᵢₙᵢₜ) ∷ (-, -, Tᵇ) ∷ []
  _ = refl

module TimedCommitment where -- (see BitML, Appendix A.5)

  t = 42 ; v = 1 ; Ha = + 9

  tc : Advertisement
  tc = ⟨ A :! v at "x" ∣∣ A :secret "a" ∣∣ B :! 0 at "y" ⟩
         reveal [ "a" ] ⇒ [ withdraw A ]
       ⊕ after t ⇒ withdraw B
       ∙

  partG = nub-participants (tc .G)

  postulate
    Tᵃ Tᵇ : TxInput -- pre-existing deposits

  valid : ValidAdvertisement tc
  valid = toWitness {Q = validAd? tc} tt

  sechash : namesˡ (tc .G) ↦ ℤ
  sechash = case_of λ where
    {- "a" -} (here _) → Ha

  txout : namesʳ (tc .G) ↦ TxInput
  txout = case_of λ where
    {- "x" -} (here _)         → Tᵃ
    {- "y" -} (there (here _)) → Tᵇ

  postulate
    Kᵃ Kᵇ : KeyPair
    Kᵈ¹ Kᵈ² Kʷᵃ : Participant → KeyPair

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} (here _)         → Kᵃ
    {- B -} (there (here _)) → Kᵇ

  K² : subterms′ (CS $ tc .C) ↦ (partG ↦ KeyPair)
  K² = case_of λ where
    {- reveal "a" ⇒ withdraw A -}
    (here _) → case_of λ where
      {- A -} (here _)         → Kᵈ² A
      {- B -} (there (here _)) → Kᵈ² B
    {- withdraw A -}
    (there (here _)) → case_of λ where
      {- A -} (here _)         → Kʷᵃ A
      {- B -} (there (here _)) → Kʷᵃ B
    {- after t ⇒ withdraw B -}
    (there (there (here _))) → case_of λ where
      {- A -} (here _)         → Kᵈ² A
      {- B -} (there (here _)) → Kᵈ² B

  K⋆ : subterms′ (CS $ tc .C) ↦ List KeyPair
  K⋆ = mapWith∈ partG ∘ K²

  e₁ : Script (Ctx 3) `Bool
  e₁ = versig (K⋆ $ here refl) ⟦ # 0 , # 1 ⟧
    `∧ `true
    `∧ ⋀ [ hash (var (# 2)) `= ` (sechash (here refl)) `∧ (` (+ η) `< ∣ var (# 2) ∣) ]

  e₂ : Script (Ctx 3) `Bool
  e₂ = versig (K⋆ $ there (there (here refl))) ⟦ # 0 , # 1 ⟧

  e′ : Script (Ctx 2) `Bool
  e′ = versig (K⋆ $ there (here refl)) ⟦ # 0 , # 1 ⟧

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs   = Tᵃ ∷ Tᵇ ∷ []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ _ , record { value = v ; validator = ƛ (e₁ `∨ e₂) }]
    ; absLock = 0 }
  Tᵢₙᵢₜ♯ = hashTx (-, -, Tᵢₙᵢₜ)

  T′ : Tx 1 1
  T′ = sig⋆ V.[ K⋆ $ here refl ] record
    { inputs  = V.[ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ _ , record { value = v ; validator = ƛ e′ }]
    ; absLock = 0 }

  T′ᵃ : Tx 1 1
  T′ᵃ = sig⋆ V.[ K⋆ $ there (here refl) ] record
    { inputs  = V.[ hashTx (-, -, T′) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ versig [ K $ here refl ] [ # 0 ] }]
    ; absLock = 0 }

  T′ᵇ : Tx 1 1
  T′ᵇ = sig⋆ V.[ K⋆ $ there (there (here refl)) ] record
    { inputs  = V.[ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ versig [ K $ there (here refl) ] [ # 0 ] }]
    ; absLock = t }

  out : ∃Tx × (subterms⁺ (CS $ tc .C) ↦ ∃Tx)
  out = bitml-compiler {g = tc .G} {ds = tc .C} valid sechash txout K K²

  outTxs : List ∃Tx
  outTxs = let t₀ , m = out in t₀ ∷ m (here refl) ∷ m (there (here refl)) ∷ m (there (there (here refl))) ∷ []

  _ : (outTxs ‼ # 0) ≡ (-, -, Tᵢₙᵢₜ)
  _ = {!refl!}

  _ : (outTxs ‼ # 1) ≡ (-, -, T′)
  _ = {!refl!}

  _ : (outTxs ‼ # 2) ≡ (-, -, T′ᵃ)
  _ = {!refl!}

  _ : (outTxs ‼ # 3) ≡ (-, -, T′ᵇ)
  _ = {!refl!}

  _ : outTxs ≡ (-, -, Tᵢₙᵢₜ) ∷ (-, -, T′) ∷ (-, -, T′ᵃ) ∷ (-, -, T′ᵇ) ∷ []
  _ = {!refl!}
