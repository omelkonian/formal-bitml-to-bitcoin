{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- Stripping sensitive information from runs (as well as other elements).
------------------------------------------------------------------------
open import Prelude.Init hiding (Σ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Lists.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces

module SymbolicModel.Stripping
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest

record Strippable (A : Set) : Set where
  field _∗ : A → A
open Strippable ⦃...⦄ public

instance
  ∗ᶜ : Strippable Configuration
  ∗ᶜ ._∗ c with c
  ... | ⟨ p ∶ a ♯ _ ⟩ = ⟨ p ∶ a ♯ nothing ⟩
  ... | l ∣ r         = l ∗ ∣ r ∗
  ... | _             = c

  ∗ᵗ : Strippable TimedConfiguration
  ∗ᵗ ._∗ (Γ at t) = (Γ ∗) at t

  ∗ˡ : Strippable Label
  ∗ˡ ._∗ l with l
  ... | auth-commit⦅ p , ad , _ ⦆ = auth-commit⦅ p , ad , [] ⦆
  ... | _                         = l

  ∗ʳ : Strippable Run
  ∗ʳ ._∗ = mapRun _∗ _∗
    where
        mapRun : (TimedConfiguration → TimedConfiguration) → (Label → Label) → (Run → Run)
        mapRun f g record { start = s ; end = .s ; trace = (.`∅ᶜ , (.s ∎)); init = init }
          = let s′ = f s in
            record {start = s′; end = s′; trace = -, (s′ ∎ₜ); init = {!init!}}
        mapRun f g record { start = start ; end = end ; trace = (.(_ ∷ _) , (.(start) —→⟨ x ⟩ x₁ ⊢ snd)) ; init = init }
          = {!!}
        -- mapRun f _ (tc ∎)        = f tc ∎
        -- mapRun f g (tc ∷⟦ α ⟧ s) = f tc ∷⟦ g α ⟧ mapRun f g s

prefixRuns : Run → List Run
prefixRuns record { start = start ; end = end ; trace = trace ; init = init } = {!!}
-- prefixRuns (tc ∙)        = [ tc ∙ ]
-- prefixRuns (tc ∷⟦ α ⟧ R) = let rs = prefixRuns R in rs ++ map (tc ∷⟦ α ⟧_) rs

-- _∈ʳ_ : Configuration → Run → Set
-- _∈ʳ_ c R = c ∈ᶜ cfg (lastCfgᵗ (R ∗))
