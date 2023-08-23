----------------------------------------------------------------------------
-- Setup for example proofs of coherence.
----------------------------------------------------------------------------
module Coherence.Example.Setup where

open import Prelude.Init public hiding (T)
open SetAsType public
open L.Mem public
open import Prelude.InferenceRules public
open import Prelude.DecEq public
open import Prelude.Decidable public
open import Prelude.Lists public
open import Prelude.Lists.Dec public
open import Prelude.Lists.Collections public
open import Prelude.Functor public
open import Prelude.Num public
open import Prelude.Membership.Patterns public
open import Prelude.Traces public
open import Prelude.ToList public

-- BitML: symbolic model
open import BitML.Example.TimedCommitment public
  using (Participant; A; B; Honest; DecEqₚ)

import BitML.BasicTypes as BitML-params
⋯′ = BitML-params.⋯_,_⋯ Participant Honest

-- Compiler
η = ℕ ∋ 128
open import Compiler ⋯′ η public
open import SecureCompilation.ComputationalContracts ⋯′ public

-- Bitcoin: computational model

import Bitcoin as BTC

finPart : Finite Participant
finPart = 2 , Fun.mk↔
  {f   = λ where A → 0F; B → 1F}
  {f⁻¹ = λ where 0F → A; 1F → B}
  ((λ where 0F → refl; 1F → refl) , (λ where A → refl; B → refl))

-- postulated cryptography
postulate Kᵃ Kᵇ K̂ᵃ K̂ᵇ : BTC.KeyPair

keypairs : Participant → BTC.KeyPair × BTC.KeyPair
keypairs A = Kᵃ , K̂ᵃ
keypairs B = Kᵇ , K̂ᵇ

-- Coherence

import SecureCompilation.ModuleParameters as SC
⋯ = SC.⋯_,_,_,_⋯ ⋯′ η finPart keypairs
open import Coherence ⋯ public

open import SymbolicModel ⋯′
  hiding (C)
open import ComputationalModel ⋯′ finPart keypairs
  renaming (K̂ to Kᵖʳⁱᵛ; K to Kᵖᵘᵇ)

module ∣K ad where
  open ∣AD ad public

  ⟨G⟩C = ad

  K : partG ↦ KeyPair
  K {x} _ = Kᵖʳⁱᵛ x

  postulate K² : subterms C ↦ partG ↦ KeyPair

-- postulated encoding
postulate
  reify-txout≡ : ∀ ad (txoutG txoutG′ : Txout ad) (txoutC txoutC′ : Txout (ad .Ad.C)) →
    ∙ txoutG ≗↦ txoutG′
    ∙ txoutC ≗↦ txoutC′
      ───────────────────────────────
      reify (ad , txoutG  , txoutC) ≡
      reify (ad , txoutG′ , txoutC′)

  instance
    -- key inequalities
    K≢ : Kᵃ ≢′ Kᵇ
    K̂≢ : K̂ᵃ ≢′ K̂ᵇ

-- helpers
encode-txout≡ : ∀ ad (txoutG txoutG′ : Txout ad) (txoutC txoutC′ : Txout (ad .Ad.C)) →
  ∙ txoutG ≗↦ txoutG′
  ∙ txoutC ≗↦ txoutC′
    ────────────────────────────────
    encodeAd ad (txoutG  , txoutC) ≡
    encodeAd ad (txoutG′ , txoutC′)
encode-txout≡ ad txoutG txoutG′ txoutC txoutC′ txoutG≗ txoutC≗ =
  cong encode (reify-txout≡ ad txoutG txoutG′ txoutC txoutC′ txoutG≗ txoutC≗)

infix 0 _at0
_at0 : Cfg → Cfgᵗ
_at0 = _at 0
