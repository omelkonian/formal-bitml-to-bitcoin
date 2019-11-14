----------------------------------------------------------------------------
-- Example contract compilations.
----------------------------------------------------------------------------
module SecureCompilation.Example where

open import Function using (_∘_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (tt)
open import Data.Product  using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Sum      using (inj₁; inj₂)
open import Data.Nat      using (ℕ; _>_; suc)
open import Data.Integer  using (ℤ; +_)
open import Data.Fin      using (0F; 1F; 2F)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Vec as V using (Vec)
open import Data.List     using (List; []; _∷_; [_]; length; allFin; map; head; tail)

open import Data.List.Relation.Unary.Any       using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Nullary.Decidable            using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

-- Bitcoin
open import Bitcoin.Crypto               using (KeyPair; HASH)
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto            using (sig⋆; hashTx; wit⊥)
open import Bitcoin.Tx.DecidableEquality using (module SETₜₓ; Set⟨Tx⟩)

-- BitML
open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)
open import BitML.BasicTypes hiding (t; a; v)
open import BitML.Contracts.Types    Participant _≟ₚ_ Honest hiding (A; B)
open import BitML.Contracts.Helpers  Participant _≟ₚ_ Honest
open import BitML.Contracts.Validity Participant _≟ₚ_ Honest using (ValidAdvertisement; validAd?)

-- BitML compiler
η = + 1
open import SecureCompilation.Compiler Participant _≟ₚ_ Honest η


module Section7 where -- (see BitML paper, Section 7).

  ex-ad : Advertisement
  ex-ad = ⟨ A :! 1 at "x" ∣∣ B :! 1 at "y" ⟩ withdraw B ∙

  postulate
    Tˣ Tʸ : TxInput -- pre-existing deposits


  valid : ValidAdvertisement ex-ad
  valid = toWitness {Q = validAd? ex-ad} tt

  sechash : ∀ {a} → inj₁ a ∈ namesᵖ (G ex-ad) → ℤ
  sechash (here ())
  sechash (there (here ()))
  sechash (there (there ()))

  txout : ∀ {d} → inj₂ d ∈ namesᵖ (G ex-ad) → TxInput
  txout (here  _)          = Tˣ
  txout (there (here _))   = Tʸ
  txout (there (there ()))

  postulate
    Kᵃ Kᵇ : KeyPair
    Kʷᵇ : Participant → KeyPair

  K : Participant → KeyPair
  K A = Kᵃ
  K B = Kᵇ

  K² : Contract → Participant → KeyPair
  K² (withdraw B) P = Kʷᵇ P
  K² _            _ = ⊥-elim impossible
    where postulate impossible : ⊥

  K⋆ : Contract → List Participant → List KeyPair
  K⋆ D = map (K² D)

  Tinit : Tx 2 1
  Tinit = record { inputs  = Tˣ V.∷ Tʸ V.∷ V.[]
                 ; wit     = wit⊥
                 ; relLock = V.replicate 0
                 ; outputs = V.[ Ctx 2 , record { value     = 2
                                                ; validator = ƛ (versig (K⋆ (withdraw B) (A ∷ B ∷ [])) (allFin _))}]
                 ; absLock = 0 }

  Tᵇ : Tx 1 1
  Tᵇ = sig⋆ V.[ K⋆ (withdraw B) (A ∷ B ∷ []) ]
            (record { inputs  = V.[ hashTx (_ , _ , Tinit) at 0 ]
                    ; wit     = wit⊥
                    ; relLock = V.replicate 0
                    ; outputs = V.[ Ctx 1 , record { value     = 2
                                                   ; validator = ƛ (versig [ K B ] [ 0F ]) }]
                    ; absLock = 0 })

  _ : {-SETₜₓ.list-} (bitml-compiler ex-ad valid sechash txout K K²)
    ≡ (_ , _ , Tinit) ∷ (_ , _ , Tᵇ) ∷ []
  _ = refl

module TimedCommitment where -- (see BitML, Appendix A.5)

  t = 42 ; v = 1 ; Ha = + 9

  tc : Advertisement
  tc = ⟨ A :! v at "x" ∣∣ A :secret "a" ∣∣ B :! 0 at "y" ⟩
         reveal [ "a" ] ⇒ [ withdraw A ]
       ⊕ after t ⇒ withdraw B
       ∙

  postulate
    Tᵃ Tᵇ : TxInput -- pre-existing deposits

  valid : ValidAdvertisement tc
  valid = toWitness {Q = validAd? tc} tt

  sechash : ∀ {a} → inj₁ a ∈ namesᵖ (G tc) → ℤ
  sechash (here ())
  sechash (there (here refl)) = Ha
  sechash (there (there (here ())))
  sechash (there (there (there ())))

  txout : ∀ {d} → inj₂ d ∈ namesᵖ (G tc) → TxInput
  txout (here  refl) = Tᵃ
  txout (there (here ()))
  txout (there (there (here refl))) = Tᵇ
  txout (there (there (there ())))

  postulate
    Kᵃ Kᵇ : KeyPair
    Kᵈ¹ Kᵈ² Kʷᵃ : Participant → KeyPair

  K : Participant → KeyPair
  K A = Kᵃ
  K B = Kᵇ

  K² : Contract → Participant → KeyPair
  K² (reveal ("a" ∷ []) ⇒ (withdraw A ∷ [])) P = Kᵈ² P
  K² (withdraw A) P                            = Kʷᵃ P
  K² (after t ⇒ withdraw B) P                  = Kᵈ² P
  K² _            _                            = ⊥-elim impossible
    where postulate impossible : ⊥

  K⋆ : Contract → List Participant → List KeyPair
  K⋆ D = map (K² D)

  e₁ : Script (Ctx 3) `Bool
  e₁ = versig (K⋆ (reveal [ "a" ] ⇒ [ withdraw A ]) (A ∷ B ∷ [])) (0F ∷ 1F ∷ [])
    `∧ `true
    `∧ ⋀ ( (hash (var 2F) `= ` (sechash (there (here refl)))
          `∧ ` η `< ∣ var 2F ∣ )
          ∷ [] )

  e₂ : Script (Ctx 3) `Bool
  e₂ = versig (K⋆ (after t ⇒ withdraw B) (A ∷ B ∷ [])) (0F ∷ 1F ∷ [])

  e′ : Script (Ctx 2) `Bool
  e′ = versig (K⋆ (withdraw A) (A ∷ B ∷ [])) (0F ∷ 1F ∷ [])

  Tinit : ∃Tx
  Tinit = 2 , 1 , record { inputs   = Tᵃ V.∷ Tᵇ V.∷ V.[]
                          ; wit     = wit⊥
                          ; relLock = V.replicate 0
                          ; outputs = V.[ _ , record { value     = v
                                                     ; validator = ƛ (e₁ `∨ e₂) }]
                          ; absLock = 0 }

  Tinit♯ = hashTx Tinit

  T′ : ∃Tx
  T′ = 1 , 1 , sig⋆ V.[ K⋆ (reveal [ "a" ] ⇒ [ withdraw A ]) (A ∷ B ∷ []) ]
                    (record { inputs  = V.[ Tinit♯ at 0 ]
                            ; wit     = wit⊥
                            ; relLock = V.replicate 0
                            ; outputs = V.[ _ , record { value     = v
                                                       ; validator = ƛ e′ }]
                            ; absLock = 0 })

  T′♯ = hashTx T′

  T′ᵃ : ∃Tx
  T′ᵃ = 1 , 1 , sig⋆ V.[ K⋆ (withdraw A) (A ∷ B ∷ []) ]
                     (record { inputs  = V.[ T′♯ at 0 ]
                             ; wit     = wit⊥
                             ; relLock = V.replicate 0
                             ; outputs = V.[ Ctx 1 , record { value     = v
                                                            ; validator = ƛ (versig [ K A ] [ 0F ]) }]
                             ; absLock = 0 })

  T′ᵇ : ∃Tx
  T′ᵇ = 1 , 1 , sig⋆ V.[ K⋆ (after t ⇒ withdraw B) (A ∷ B ∷ []) ]
                     (record { inputs  = V.[ Tinit♯ at 0 ]
                             ; wit     = wit⊥
                             ; relLock = V.replicate 0
                             ; outputs = V.[ Ctx 1 , record { value     = v
                                                            ; validator = ƛ (versig [ K B ] [ 0F ]) }]
                             ; absLock = t })

  _ : {-SETₜₓ.list-} (bitml-compiler tc valid sechash txout K K²)
    ≡ (Tinit ∷ T′ ∷ T′ᵃ ∷ T′ᵇ ∷ [])
  _ = refl
