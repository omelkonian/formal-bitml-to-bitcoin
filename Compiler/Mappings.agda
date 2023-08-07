open import Prelude.Init; open SetAsType
open import Prelude.Lists.Mappings
open import Prelude.Lists.Collections

open import Bitcoin
open import BitML.BasicTypes using (⋯)

module Compiler.Mappings (⋯ : ⋯) where

open import BitML ⋯

private variable X : Type

Txout : ⦃ X has Name ⦄ → X → Type
Txout x = ids x ↦ TxInput′

Sechash : ⦃ X has Name ⦄ → X → Type
Sechash x = secrets x ↦ HashId

𝕂 : Precondition → Type
𝕂 g = nub-participants g ↦ KeyPair

𝕂²′ : Ad → Type
𝕂²′ (⟨ g ⟩ c) = subterms c ↦ 𝕂 g

𝕂² : ⦃ X has Ad ⦄ → X → Type
𝕂² x = advertisements x ↦′ 𝕂²′
