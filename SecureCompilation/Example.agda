----------------------------------------------------------------------------
-- Example compilation of a simple contract (see BitML paper, Section 7).
----------------------------------------------------------------------------
module SecureCompilation.Example where

open import Level using (0ℓ)

open import Data.Nat     using (ℕ; _>_)
open import Data.List    using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)

open import Relation.Binary  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists

data Participant : Set where
  A B : Participant

{-

ex-ad : Advertisement 2 [] [] (1 ∷ 1 ∷ [])
ex-ad = ⟨ A :! 1 ∣ B :! 1 ⟩ withdraw B ∙ ∶- {!!}

_ :
  let Tx    = {!!}
      Ty    = {!!}

      Tb-v  : State → UTxO-Value → PendingTx → ⊤ → ⊤ → Bool
      Tb-v  = λ _ _ _ _ _ → {!!}

      Tinit = record { inputs  =  Tx ∷ Ty ∷ []
                     ; outputs = [ record { value      = $ 2
                                          ; address    = {!Tb-v ♯!}
                                          ; Data       = UNIT
                                          ; dataScript = const tt } ]
                     ; forge   = $0
                     ; fee     = $0 }
      Tb    = record { inputs  = [ (record { outputRef = (Tinit ♯ₜₓ) indexed-at 0
                                           ; R = UNIT
                                           ; D = UNIT
                                           ; redeemer = const tt
                                           ; validator = Tb-v }) ]
                     ; outputs =  [ {!!} ]
                     ; forge   = $0
                     ; fee     = $0 }
  in bitml-compiler ex-ad ≡ (Tinit ∷ Tb ∷ [])
_ = {!refl!}

-}
