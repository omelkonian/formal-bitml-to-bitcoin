------------------------------------------------------------------------
-- Lemmas related to BitML's computational model.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Membership

open import Bitcoin.Crypto using (KeyPair)

module ComputationalModel.Lemmas
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)
  where

open import ComputationalModel.Strategy Participant Honest finPart keypairs

----------------------------------------
-- Lemma 5

module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open AdvM Adv Adv∉

  MaximalRun : Strategies → Run → Set
  MaximalRun SS R = (R -conforms-to- SS)
                  × (¬ ∃ λ R′ → (R′ -conforms-to- SS)
                              × (length R′ > length R))

  unique-maximal-run :
      MaximalRun SS R
    → MaximalRun SS R′
      ----------------
    → R ≡ R′
  unique-maximal-run = {!!}
