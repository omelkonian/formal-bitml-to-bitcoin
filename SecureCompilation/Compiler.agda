----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level    using (0ℓ)
open import Function using (const)

open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Bool     using (Bool; true; false)
open import Data.Nat      using (ℕ; _+_; _>_)
open import Data.List     using (List; []; _∷_; length; map; concatMap; sum)
open import Data.Vec as V using ()

open import Relation.Binary  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

-- Bitcoin
open import Bitcoin.BasicTypes
  using ($)
open import Bitcoin.Tx.Base
  using ( TxInput
        ; ∃Tx
        )
open import Bitcoin.Tx.DecidableEquality
  using (module SETₜₓ; Set⟨Tx⟩)

module SecureCompilation.Compiler
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

-- BitML
open import BitML.BasicTypes      Participant _≟ₚ_ Honest
  using ( Time
        ; Value
        ; Values
        ; Iᵖ[_,_]
        )
open import BitML.Contracts.Types Participant _≟ₚ_ Honest
  using ( Iᶜ[_,_]
        ; ci; Contract; ∃Contract
        ; put_&reveal_if_⇒_∶-_; withdraw; split_∶-_; _∶_; after_∶_
        ; ∃Contracts
        ; ⟨_⟩_∶-_; ∃Advertisement
        ; participantsᵍ; toStipulate
        )

--------------------------------------------

bitml-compiler : ∃Advertisement → Set⟨Tx⟩
bitml-compiler (_ , Iᵖ[ _ , vsᵖ ] , (⟨ G ⟩ C ∶- _))
  = SETₜₓ.fromList (Tinit ∷ concatMap compileChoice C)
  where
    partG : List Participant
    partG = participantsᵍ G

    V : Value
    V = sum vsᵖ -- (map proj₂ (toStipulate G))

    txout : Participant × Value → TxInput
    txout (p , vp) = record { txId  = {!!}
                            ; index = 0 }

    Tinit : ∃Tx
    Tinit = _ , _ , record { inputs  = V.fromList (map txout (toStipulate G))
                           ; wit     = V.replicate (_ , V.[])
                           ; relLock = {!!}
                           ; outputs = V.[ {!!} , record { value     = $ V
                                                         ; validator = {!!} } ]
                           ; absLock = {!!} }

    Bc : ∃Contracts
       → ∃Contract
       → ∃Tx
       → ℕ
       → Value
       → Values
       → List Participant
       → Time
       → List ∃Tx
    Bd : ∃Contract
       → ∃Contract
       → ∃Tx
       → ℕ
       → Value
       → List Participant
       → Time
       → List ∃Tx

    Bc C Dp T o v I P t = {!!}

    Bd (_ , (put zs &reveal as if p ⇒ C ∶- _)) Dp T o v P t = Bc (_ , C) Dp T o (v + {!!}) zs P t
    Bd (_ , (withdraw A)) Dp T o v P t = {!!}
    Bd (_ , (split cs ∶- _)) Dp T o v P t = {!!}
    Bd (_ , (A ∶ D′)) Dp T o v P t = {!!}
    Bd (_ , (after t′ ∶ D′)) Dp T o v P t = {!!}

    compileChoice : Contract ci → List ∃Tx
    compileChoice Di = Bd (_ , Di) (_ , Di) Tinit 0 V partG 0
