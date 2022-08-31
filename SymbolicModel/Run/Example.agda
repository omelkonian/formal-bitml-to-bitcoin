module SymbolicModel.Run.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Decidable

open import BitML.Example.Setup using (Participant; Honest; A; B)
open import BitML.Example.TimedCommitment using (tc-stepsₜ)
open import BitML Participant Honest hiding (A; B; x; y; a)
open import SymbolicModel.Run.Base Participant Honest

x = "x"; y = "y"; x₃ = "x₃"; a = "CHANGE_ME"; N = 9

tc-run : Run
tc-run = record
  { start = (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  ; init  = auto
  ; end   = (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
  ; trace = -, tc-stepsₜ
  }
