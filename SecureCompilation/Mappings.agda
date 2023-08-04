open import Prelude.Init; open SetAsType
open import Prelude.Lists.Mappings
open import Prelude.Lists.Collections

open import Bitcoin
open import BitML.BasicTypes using (⋯)

module SecureCompilation.Mappings (⋯ : ⋯) where

open import BitML ⋯

private variable X : Type

Txout : ⦃ X has Name ⦄ → Pred₀ X
Txout x = namesʳ x ↦ TxInput′

Sechash : ⦃ X has Name ⦄ → Pred₀ X
Sechash x = namesˡ x ↦ ℤ

𝕂 : Pred₀ Precondition
𝕂 g = nub-participants g ↦ KeyPair

𝕂²′ : Pred₀ Ad
𝕂²′ (⟨ g ⟩ c) = subtermsᶜ′ c ↦ nub-participants g ↦ KeyPair

𝕂² : ⦃ X has Ad ⦄ → Pred₀ X
𝕂² x = advertisements x ↦′ 𝕂²′
