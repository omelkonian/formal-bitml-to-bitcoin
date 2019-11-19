------------------------------------------------------------------------
-- Lemmas related to BitML's computational model.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Nat     using (_>_)
open import Data.List    using (List; length)

open import Data.List.Membership.Propositional using (_∉_)

open import Relation.Nullary                      using (¬_)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists

open import Bitcoin.Crypto using (KeyPair)

module ComputationalModel.Lemmas
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)
  where

open import ComputationalModel.Strategy Participant _≟ₚ_ Honest finPart keypairs

----------------------------------------
-- Lemma 5

module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open AdvM Adv Adv∉

  MaximalRun : Strategies → Run → Set
  MaximalRun SS R = (R -conforms-to- SS)
                  × (¬ ∃[ R′ ] ( (R′ -conforms-to- SS)
                               × (length R′ > length R) ))

  unique-maximal-run :
      MaximalRun SS R
    → MaximalRun SS R′
      ----------------
    → R ≡ R′
  unique-maximal-run = {!!}
