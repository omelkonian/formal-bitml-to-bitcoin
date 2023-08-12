----------------------------------------------------------------------------
-- Example contract compilation.
----------------------------------------------------------------------------
module Compiler.Example where

open import Prelude.Init hiding (T); open SetAsType
open import Prelude.Lists
open import Prelude.Membership.Patterns
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Num


-- Bitcoin
open import Bitcoin hiding (t; Value)

-- BitML
open import BitML.Example.TimedCommitment
  using (Participant; A; B; Honest)
import BitML.BasicTypes as BitML-params
⋯ = BitML-params.⋯_,_⋯ Participant Honest
open import BitML ⋯
  hiding ( C; G; t; a; v; A; B; x; y; Γ₀; Γₜ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′
         ; _`=_; _`∧_; _`∨_; `_; `true; _`<_
         )

-- BitML compiler
η = ℕ ∋ 128
open import Compiler ⋯ η

-- postulated cryptography
module ∣K ad where
  open ∣AD ad public

  postulate
    K  : partG ↦ KeyPair
    K² : subterms C ↦ partG ↦ KeyPair

module Section7 where -- (see BitML paper, Section 7).

  module Withdraw where
    ex-ad : Ad
    ex-ad = ⟨ A :! 1 𝐁 at "x" ∣ B :! 1 𝐁 at "y" ⟩ [ withdraw B ]

    open ∣K ex-ad

    T₀ : Tx 0 2
    T₀ = record
      { inputs  = []
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ (1 , 1 𝐁 locked-by ƛ (versig [ K 0 ] [ 0 ]))
                  ⨾ (1 , 1 𝐁 locked-by ƛ (versig [ K 1 ] [ 0 ]))
                  ]
      ; absLock = 0 }

    Tˣ Tʸ : TxInput′
    Tˣ = (-, -, T₀) at 0
    Tʸ = (-, -, T₀) at 1

    sechash : secrets G ↦ ℤ
    sechash ()

    txout : ids G ↦ TxInput′
    txout = λ where
      {- "x" -} 𝟘 → Tˣ
      {- "y" -} 𝟙 → Tʸ

    out : InitTx G × (subterms⁺ C ↦′ BranchTx)
    out = bitml-compiler {ad = ex-ad} auto sechash txout K K²

    outTxs : Tx 2 1 × Tx 1 1
    outTxs = let t₀ , m = out in t₀ , m 0

    Tᵢₙᵢₜ : Tx 2 1
    Tᵢₙᵢₜ = sig⋆ [ [ K 0 ] ⨾ [ K 1 ] ] record
      { inputs  = hashTxⁱ <$> [ Tˣ ⨾ Tʸ ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 2 , 2 𝐁 locked-by ƛ versig (codom $ K² 0) [ 0 ⨾ 1 ] ]
      ; absLock = 0 }
    Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

    Tᵇ : Tx 1 1
    Tᵇ = sig⋆ [ codom (K² 0) ] record
      { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 1 , 2 𝐁 locked-by ƛ versig [ K 1 ] [ 0 ] ]
      ; absLock = 0 }

    _ = outTxs ≡ (Tᵢₙᵢₜ , Tᵇ)
      ∋ refl

  module Split where
    ex-ad : Ad
    ex-ad = ⟨ A :! 2 𝐁 at "x" ∣ B :! 1 𝐁 at "y" ⟩
            [ split (1 𝐁 ⊸ withdraw A ⊗ 2 𝐁 ⊸ withdraw B) ]

    open ∣K ex-ad

    T₀ : Tx 0 2
    T₀ = record
      { inputs  = []
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ (2 , 1 𝐁 locked-by ƛ (versig [ K 0 ] [ 0 ]))
                  ⨾ (1 , 1 𝐁 locked-by ƛ (versig [ K 1 ] [ 0 ]))
                  ]
      ; absLock = 0 }

    -- pre-existing deposits
    Tˣ Tʸ : TxInput′
    Tˣ = (-, -, T₀) at 0
    Tʸ = (-, -, T₀) at 1

    sechash : secrets G ↦ ℤ
    sechash ()

    txout : ids G ↦ TxInput′
    txout = λ where
      {- "x" -} 𝟘 → Tˣ
      {- "y" -} 𝟙 → Tʸ

    out : InitTx G × (subterms⁺ C ↦′ BranchTx)
    out = bitml-compiler {ad = ex-ad} auto sechash txout K K²

    outTxs : Tx 2 1 × Tx 1 2 × Tx 1 1 × Tx 1 1
    outTxs = let t₀ , m = out in t₀ , m 0 , m 1 , m 2

    Tᵢₙᵢₜ : Tx 2 1
    Tᵢₙᵢₜ = sig⋆ [ [ K 0 ] ⨾ [ K 1 ] ] record
      { inputs  = hashTxⁱ <$> [ Tˣ ⨾ Tʸ ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 2 , 3 𝐁 locked-by ƛ versig (codom $ K² 0) [ 0 ⨾ 1 ] ]
      ; absLock = 0 }
    Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

    Tₛₚₗᵢₜ : Tx 1 2
    Tₛₚₗᵢₜ = sig⋆ [ codom (K² 0) ] record
      { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 2 , 1 𝐁 locked-by ƛ versig (codom $ K² 1) [ 0 ⨾ 1 ]
                  ⨾ 2 , 2 𝐁 locked-by ƛ versig (codom $ K² 2) [ 0 ⨾ 1 ]
                  ]
      ; absLock = 0 }
    Tₛₚₗᵢₜ♯ = (∃Tx ∋ -, -, Tₛₚₗᵢₜ) ♯

    Tᵃ : Tx 1 1
    Tᵃ = sig⋆ [ codom (K² 1) ] record
      { inputs  = [ Tₛₚₗᵢₜ♯ at 0 ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 1 , 1 𝐁 locked-by ƛ versig [ K 0 ] [ 0 ] ]
      ; absLock = 0 }

    Tᵇ : Tx 1 1
    Tᵇ = sig⋆ [ codom (K² 2) ] record
      { inputs  = [ Tₛₚₗᵢₜ♯ at 1 ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 1 , 2 𝐁 locked-by ƛ versig [ K 1 ] [ 0 ] ]
      ; absLock = 0 }

    _ = outTxs ≡ (Tᵢₙᵢₜ , Tₛₚₗᵢₜ , Tᵃ , Tᵇ)
      ∋ refl

  module Put where
    ex-ad : Ad
    ex-ad = ⟨ A :? 1 𝐁 at "x" ∣ A :! 1 𝐁 at "y" ∣ B :! 1 𝐁 at "z" ⟩
            [ put "x" ． withdraw B ]

    open ∣K ex-ad

    T₀ : Tx 0 3
    T₀ = record
      { inputs  = []
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ (1 , 1 𝐁 locked-by ƛ (versig [ K 0 ] [ 0 ]))
                  ⨾ (1 , 1 𝐁 locked-by ƛ (versig [ K 0 ] [ 0 ]))
                  ⨾ (1 , 1 𝐁 locked-by ƛ (versig [ K 1 ] [ 0 ]))
                  ]
      ; absLock = 0 }

    -- pre-existing deposits
    Tˣ Tʸ Tᶻ : TxInput′
    Tˣ = (-, -, T₀) at 0
    Tʸ = (-, -, T₀) at 1
    Tᶻ = (-, -, T₀) at 2

    sechash : secrets G ↦ ℤ
    sechash ()

    txout : ids G ↦ TxInput′
    txout = λ where
      {- "x" -} 𝟘 → Tˣ
      {- "y" -} 𝟙 → Tʸ
      {- "z" -} 𝟚 → Tᶻ

    out : InitTx G × (subterms⁺ C ↦′ BranchTx)
    out = bitml-compiler {ad = ex-ad} auto sechash txout K K²

    outTxs : Tx 2 1 × Tx 2 1 × Tx 1 1
    outTxs = let t₀ , m = out in t₀ , m 0 , m 1

    Tᵢₙᵢₜ : Tx 2 1
    Tᵢₙᵢₜ = sig⋆ [ [ K 0 ] ⨾ [ K 1 ] ] record
      { inputs  = hashTxⁱ <$> [ Tʸ ⨾ Tᶻ ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 2 , 2 𝐁 locked-by ƛ versig (codom $ K² 0) [ 0 ⨾ 1 ]
                                      `∧ `true `∧ `true ]
      ; absLock = 0 }
    Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

    Tₚᵤₜ : Tx 2 1
    Tₚᵤₜ = sig⋆ [ codom (K² 0) ⨾ [ K 0 ] ] record
      { inputs  = [ Tᵢₙᵢₜ♯ at 0 ⨾ hashTxⁱ Tˣ ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 2 , 3 𝐁 locked-by ƛ versig (codom $ K² 1) [ 0 ⨾ 1 ] ]
      ; absLock = 0 }
    Tₚᵤₜ♯ = (∃Tx ∋ -, -, Tₚᵤₜ) ♯

    Tᵃ : Tx 1 1
    Tᵃ = sig⋆ [ codom (K² 1) ] record
      { inputs  = [ Tₚᵤₜ♯ at 0 ]
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ 1 , 3 𝐁 locked-by ƛ versig [ K 1 ] [ 0 ] ]
      ; absLock = 0 }

    _ = outTxs ≡ (Tᵢₙᵢₜ , Tₚᵤₜ , Tᵃ)
      ∋ refl

module TimedCommitment where -- (see BitML, Section 7 and Appendix A.5)

  open import BitML.Example.TimedCommitment

  open ∣K TC

  v = Value ∋ 1 ; a♯ = + 9 -- constants

  T₀ : Tx 0 2
  T₀ = record
    { inputs  = []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ (1 , v locked-by ƛ versig [ K 0 ] [ 0 ])
                ⨾ (1 , 0 locked-by ƛ versig [ K 1 ] [ 0 ])
                ]
    ; absLock = 0 }

  -- pre-existing deposits
  Tᵃ Tᵇ : TxInput′
  Tᵃ = (-, -, T₀) at 0
  Tᵇ = (-, -, T₀) at 1

  sechash : secrets G ↦ ℤ
  sechash = λ where
    {- "a" -} 𝟘 → a♯

  txout : ids G ↦ TxInput′
  txout = λ where
    {- "x" -} 𝟘 → Tᵃ
    {- "y" -} 𝟙 → Tᵇ

  out : InitTx G × (subterms⁺ C ↦′ BranchTx)
  out = bitml-compiler {ad = TC} auto sechash txout K K²

  outTxs : Tx 2 1 × Tx 1 1 × Tx 1 1 × Tx 1 1
  outTxs = let t₀ , m = out in t₀ , m 0 , m 1 , m 2

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = sig⋆ [ [ K 0 ] ⨾ [ K 1 ] ] record
    { inputs  = hashTxⁱ <$> [ Tᵃ ⨾ Tᵇ ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ -, v locked-by ƛ (e₁ `∨ e₂)]
    ; absLock = 0 }
    where
      e₁ : Script 3 `Bool
      e₁ = versig (codom $ K² 0) [ 0 ⨾ 1 ]
        `∧ `true
        `∧ ⋀ [ hash (var 2) `= ` (sechash 0) `∧ (` (+ η) `< ∣ var 2 ∣) ]

      e₂ : Script 3 `Bool
      e₂ = versig (codom $ K² 2) [ 0 ⨾ 1 ]
  Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

  T′ : Tx 1 1
  T′ = sig⋆ [ codom (K² 0) ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ _ , v locked-by ƛ e′ ]
    ; absLock = 0 }
    where
      e′ : Script 2 `Bool
      e′ = versig (codom $ K² 1) [ 0 ⨾ 1 ]
  T′♯ = (∃Tx ∋ -, -, T′) ♯

  T′ᵃ : Tx 1 1
  T′ᵃ = sig⋆ [ codom (K² 1) ] record
    { inputs  = [ T′♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , v locked-by ƛ versig [ K 0 ] [ 0 ] ]
    ; absLock = 0 }

  T′ᵇ : Tx 1 1
  T′ᵇ = sig⋆ [ codom (K² 2) ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , v locked-by ƛ versig [ K 1 ] [ 0 ] ]
    ; absLock = t }

  _ = outTxs ≡ (Tᵢₙᵢₜ , T′ , T′ᵃ , T′ᵇ)
    ∋ refl
