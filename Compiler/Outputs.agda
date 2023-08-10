open import Prelude.Init; open SetAsType

open import Bitcoin using (Tx)

open import BitML.BasicTypes using (⋯)

module Compiler.Outputs (⋯ : ⋯) where

open import BitML ⋯

-- type of initial transaction
InitTx : Precondition → Type
InitTx g = Tx (length $ persistentIds g) 1

-- type of subterm transactions
BranchTx : Branch → Type
BranchTx d
  with _ ← decorations∘remove≡[] {d}
  with removeTopDecorations d
... | put xs &reveal _ if _ ⇒ c = Tx (suc $ length xs) 1
... | split vcs                 = Tx 1 (length vcs)
... | withdraw _                = Tx 1 1
