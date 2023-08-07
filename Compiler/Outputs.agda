open import Prelude.Init; open SetAsType

open import Bitcoin

open import BitML.BasicTypes using (⋯)

module Compiler.Outputs (⋯ : ⋯) where

open import BitML ⋯

-- single-output transactions
Tx¹ : ℕ → Type
Tx¹ i = Tx i 1
∃Tx¹ = ∃ Tx¹

-- contract-dependent outputs
outputLen : Branch → ℕ
outputLen = λ where
  (split vcs) → length vcs
  _           → 1

Txᵈ : ℕ → Branch → Type
Txᵈ i c = Tx i (outputLen c)

∃Txᵈ : Branch → Type
∃Txᵈ c = ∃ λ i → Txᵈ i c
