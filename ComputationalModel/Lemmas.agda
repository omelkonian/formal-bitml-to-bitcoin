------------------------------------------------------------------------
-- Lemmas related to BitML's computational model.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Membership
open import Prelude.ToList
open import Prelude.InferenceRules

open import Bitcoin.Crypto using (KeyPair)
open import BitML.BasicTypes using (⋯)

module ComputationalModel.Lemmas
  (⋯ : ⋯) (let open ⋯ ⋯)
  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)
  where

open import ComputationalModel.Strategy ⋯ finPart keypairs

----------------------------------------
-- Lemma 5

module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open AdvM Adv Adv∉

  MaximalRun : Strategies → CRun → Set
  MaximalRun SS R = (R -conforms-to- SS)
                  × (¬ ∃ λ R′ → (R′ -conforms-to- SS)
                              × (length (toList R′) > length (toList R)))

  unique-maximal-run : ∀ {R R′} →
    ∙ MaximalRun SS R
    ∙ MaximalRun SS R′
      ────────────────
      R ≡ R′
  unique-maximal-run = {!!}
