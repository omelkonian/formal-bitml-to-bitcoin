----------------------------------------------------------------------------
-- Example contract compilation.
----------------------------------------------------------------------------
module Compiler.Example where

open import Prelude.Init hiding (T); open SetAsType
open L.Mem using (mapWith∈)
open import Prelude.Lists
open import Prelude.Membership.Patterns
open import Prelude.Functor
open import Prelude.Decidable

-- BitML
open import BitML.Example.TimedCommitment
  using (Participant; A; B; Honest)
import BitML.BasicTypes as BitML-params
⋯ = BitML-params.⋯_,_⋯ Participant Honest
open import BitML ⋯
  hiding ( t; a; v; A; B; x; y; x′; y′; Γ₀; Γₜ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′
         ; _`=_; _`∧_; _`∨_; `_; `true; _`<_
         )

-- BitML compiler
η = 1024
open import Compiler ⋯ η

finPart : Finite Participant
finPart = 2 , Fun.mk↔
  {f   = λ where A → 0F; B → 1F}
  {f⁻¹ = λ where 0F → A; 1F → B}
  ((λ where 0F → refl; 1F → refl) , (λ where A → refl; B → refl))

-- Bitcoin
open import Bitcoin hiding (t)
postulate Kᵃ Kᵇ K̂ᵃ K̂ᵇ : KeyPair

module Section7 where -- (see BitML paper, Section 7).

  x = "x"; y = "y"; x′ = "x′"; y′ = "y′"; x₁ = "x₁"

  ex-ad : Ad
  ex-ad = ⟨ A :! 1 at x ∣ B :! 1 at y ⟩ [ withdraw B ]

  partG = nub-participants (ex-ad .G)

  postulate Kʷᵇ : Participant → KeyPair

  T₀ : Tx 0 2
  T₀ = record
    { inputs  = []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ (1 , 1 locked-by ƛ (versig [ K̂ᵃ ] [ # 0 ]))
                ⨾ (1 , 1 locked-by ƛ (versig [ K̂ᵇ ] [ # 0 ]))
                ]
    ; absLock = 0 }

  -- pre-existing deposits
  Tˣ Tʸ : TxInput′
  Tˣ = (-, -, T₀) at 0F
  Tʸ = (-, -, T₀) at 1F

  sechash : namesˡ (ex-ad .G) ↦ ℤ
  sechash ()

  txout : namesʳ (ex-ad .G) ↦ TxInput′
  txout = case_of λ where
    {- "x" -} 𝟘 → Tˣ
    {- "y" -} 𝟙 → Tʸ

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} 𝟘 → Kᵃ
    {- B -} 𝟙 → Kᵇ

  K² : subterms (ex-ad .C) ↦ (partG ↦ KeyPair)
  K² = case_of λ where
    𝟘 → case_of λ where
      {- A -} 𝟘 → Kʷᵇ A
      {- B -} 𝟙 → Kʷᵇ B

  Ks : List KeyPair
  Ks = mapWith∈ partG (K² $ here refl)

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs  = hashTxⁱ <$> [ Tˣ ⨾ Tʸ ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 2 , 2 locked-by ƛ versig Ks (allFin _)]
    ; absLock = 0 }
  Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

  Tᵇ : Tx 1 1
  Tᵇ = sig⋆ [ Ks ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , 2 locked-by ƛ versig [ K (there (here refl)) ] [ 0F ] ]
    ; absLock = 0 }

  out : ∃Tx¹ × (subterms⁺ ex-ad ↦′ ∃Txᵈ)
  out = bitml-compiler {ad = ex-ad} auto sechash txout K K²

  outTxs : Tx 2 1 × Tx 1 1
  outTxs = let t₀ , m = out in t₀ .proj₂ , m 𝟘 .proj₂

  _ = outTxs ≡ (Tᵢₙᵢₜ , Tᵇ)
    ∋ refl

module TimedCommitment where -- (see BitML, Appendix A.5)

  open import BitML.Example.TimedCommitment

  -- t = 42 ;
  v = 1 ; Ha = + 9

  partG = nub-participants (TC .G)

  postulate Kᵈ¹ Kᵈ² Kʷᵃ : Participant → KeyPair

  T₀ : Tx 0 2
  T₀ = record
    { inputs  = []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ (1 , 1 locked-by ƛ (versig [ K̂ᵃ ] [ # 0 ]))
                ⨾ (1 , 0 locked-by ƛ (versig [ K̂ᵇ ] [ # 0 ]))
                ]
    ; absLock = 0 }

  -- pre-existing deposits
  Tᵃ Tᵇ : TxInput′
  Tᵃ = (-, -, T₀) at 0F
  Tᵇ = (-, -, T₀) at 1F

  sechash : namesˡ (TC .G) ↦ ℤ
  sechash = case_of λ where
    {- "a" -} 𝟘 → Ha

  txout : namesʳ (TC .G) ↦ TxInput′
  txout = case_of λ where
    {- "x" -} 𝟘 → Tᵃ
    {- "y" -} 𝟙 → Tᵇ

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} 𝟘 → Kᵃ
    {- B -} 𝟙 → Kᵇ

  K² : subterms (TC .C) ↦ (partG ↦ KeyPair)
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

  K⋆ : subterms (TC .C) ↦ List KeyPair
  K⋆ = mapWith∈ partG ∘ K²

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs  = hashTxⁱ <$> [ Tᵃ ⨾ Tᵇ ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ _ , v locked-by ƛ (e₁ `∨ e₂)]
    ; absLock = 0 }
    where
      e₁ : Script 3 `Bool
      e₁ = versig (K⋆ 𝟘) [ # 0 ⨾ # 1 ]
        `∧ `true
        `∧ ⋀ [ hash (var (# 2)) `= ` (sechash 𝟘) `∧ (` (+ η) `< ∣ var (# 2) ∣) ]

      e₂ : Script 3 `Bool
      e₂ = versig (K⋆ 𝟚) [ # 0 ⨾ # 1 ]
  Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

  T′ : Tx 1 1
  T′ = sig⋆ [ K⋆ 𝟘 ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ _ , v locked-by ƛ e′ ]
    ; absLock = 0 }
    where
      e′ : Script 2 `Bool
      e′ = versig (K⋆ 𝟙) [ # 0 ⨾ # 1 ]

  T′ᵃ : Tx 1 1
  T′ᵃ = sig⋆ [ K⋆ 𝟙 ] record
    { inputs  = [ ((∃Tx ∋ -, -, T′) ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , v locked-by ƛ versig [ K 𝟘 ] [ # 0 ] ]
    ; absLock = 0 }

  T′ᵇ : Tx 1 1
  T′ᵇ = sig⋆ [ K⋆ 𝟚 ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , v locked-by ƛ versig [ K 𝟙 ] [ # 0 ] ]
    ; absLock = t }

  out : ∃Tx¹ × (subterms⁺ TC ↦′ ∃Txᵈ)
  out = bitml-compiler {ad = TC} auto sechash txout K K²

  outTxs : Tx 2 1 × Tx 1 1 × Tx 1 1 × Tx 1 1
  outTxs = let t₀ , m = out in
      t₀ .proj₂
    , m 𝟘 .proj₂
    , m 𝟙 .proj₂
    , m 𝟚 .proj₂

  _ = outTxs ≡ (Tᵢₙᵢₜ , T′ , T′ᵃ , T′ᵇ)
    ∋ refl
