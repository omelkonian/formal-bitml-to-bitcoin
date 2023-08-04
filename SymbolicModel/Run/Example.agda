module SymbolicModel.Run.Example where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Decidable

open import BitML.Example.TimedCommitment
  using (Participant; A; B; Honest; x; y; x₃; a; N; TC-stepsₜ)
open import BitML.BasicTypes using (⋯_,_⋯)
open import BitML ⋯ Participant , Honest ⋯
  hiding (A; B; x; y; a)
open import SymbolicModel.Run.Base ⋯ Participant , Honest ⋯

TC-run : Run
TC-run = record
  { start = (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  ; init  = auto
  ; end   = (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
  ; trace = -, TC-stepsₜ
  }
