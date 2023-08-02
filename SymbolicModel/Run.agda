------------------------------------------------------------------------
-- Symbolic runs.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq

open import BitML.BasicTypes using (⋯)

module SymbolicModel.Run (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML ⋯ public -- re-export all BitML definitions
open import SymbolicModel.Run.Base ⋯ public
open import SymbolicModel.Run.Properties ⋯ public
open import SymbolicModel.Run.Example
