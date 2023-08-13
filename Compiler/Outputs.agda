open import Prelude.Init; open SetAsType

open import Bitcoin using (Tx)

open import BitML.BasicTypes using (⋯)

module Compiler.Outputs (⋯ : ⋯) where

open import BitML ⋯

-- type of initial transaction
InitTx : Precondition → Type
InitTx g = Tx (length $ persistentIds g) 1

-- type of subterm transactions
Inᵈ Outᵈ : Branch → ℕ
Inᵈ = removeTopDecorations >≡> λ where
  (put xs &reveal _ if _ ⇒ _) → suc $ length xs
  _ → 1
Outᵈ = removeTopDecorations >≡> λ where
  (split vcs) → length vcs
  _ → 1

BranchTx : Branch → Type
BranchTx d = Tx (Inᵈ d) (Outᵈ d)
--   with _ ← decorations∘remove≡[] {d}
--   with removeTopDecorations d
-- ... | put xs &reveal _ if _ ⇒ c = Tx (suc $ length xs) 1
-- ... | split vcs                 = Tx 1                 (length vcs)
-- ... | withdraw _                = Tx 1                 1
