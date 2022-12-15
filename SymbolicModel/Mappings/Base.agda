open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Validity
open import Prelude.Lists.Collections
open import Prelude.InferenceRules
open import Prelude.Traces

open import Bitcoin

module SymbolicModel.Mappings.Base
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest
open import SymbolicModel.Accessors Participant Honest
open import SymbolicModel.Collections Participant Honest

private variable X : Set ℓ

Txout : ⦃ X has Name ⦄ → Pred₀ X
Txout x = namesʳ x ↦ TxInput′

Sechash : ⦃ X has Name ⦄ → Pred₀ X
Sechash x = namesˡ x ↦ ℤ

𝕂 : Pred₀ Precondition
𝕂 g = nub-participants g ↦ KeyPair

𝕂²′ : Pred₀ Advertisement
𝕂²′ (⟨ g ⟩ c) = subtermsᶜ′ c ↦ nub-participants g ↦ KeyPair

𝕂² : ⦃ X has Advertisement ⦄ → Pred₀ X
𝕂² x = advertisements x ↦′ 𝕂²′

-- Well-formed terms, where we can provide mappings txout,sechash,κ.
record 𝕎 ⦃ _ : X has Name ⦄ ⦃ _ : X has Advertisement ⦄ (x : X) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txout   : Txout   x
    sechash : Sechash x
    κ       : 𝕂²      x

ℝ = Pred₀ Run ∋ 𝕎
module ℝ (𝕣 : ℝ R) where
  open 𝕎 𝕣 public renaming (txout to txout′; sechash to sechash′; κ to κ′)

instance
  ℝ∙Cfg : (ℝ R) ∙Cfg
  ℝ∙Cfg {R = R} = ∙cfg= (const $ R ∙cfg)

ℾᵗ = Pred₀ Cfgᵗ ∋ 𝕎
module ℾᵗ (ℽ : ℾᵗ Γₜ) where
  open 𝕎 ℽ public renaming (txout to txoutΓ; sechash to sechashΓ; κ to κΓ)

ℾᵗ-∅ᵗ : ℾᵗ ∅ᵗ
ℾᵗ-∅ᵗ = record {txout = λ (); sechash = λ (); κ = λ ()}

ℾ = Pred₀ Cfg ∋ 𝕎
module ℾ (ℽ : ℾ Γ) where
  open 𝕎 ℽ public renaming (txout to txoutΓ; sechash to sechashΓ; κ to κΓ)

ℾ-∅ : ℾ ∅ᶜ
ℾ-∅ = record {txout = λ (); sechash = λ (); κ = λ ()}

𝔾 : Pred₀ Ad
𝔾 ad = Valid ad × Txout (ad .G) × Sechash (ad .G) × 𝕂²′ ad
