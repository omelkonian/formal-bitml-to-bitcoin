module SymbolicModel.Run.Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Decidable

open import BitML.Example.Setup using (Participant; Honest; A; B)
import BitML as BitML
open import BitML BitML.⋯ Participant , Honest ⋯
  hiding (A; B; x; y; a)
open import SymbolicModel.Run.Base BitML.⋯ Participant , Honest ⋯
open import BitML.Example.TimedCommitment using (x; y; x₃; a; N; TC-stepsₜ)

TC-run : Run
TC-run = record
  { start = (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  ; init  = auto
  ; end   = (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
  ; trace = -, TC-stepsₜ
  }
