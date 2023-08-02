open import Prelude.Init
open import Prelude.DecEq

open import BitML.BasicTypes using (⋯)

module SymbolicModel (⋯ : ⋯) where

open import SymbolicModel.Run ⋯ public
open import SymbolicModel.Accessors ⋯ public
open import SymbolicModel.Collections ⋯ public
open import SymbolicModel.Mappings ⋯ public
open import SymbolicModel.ValuePreservation ⋯ public
open import SymbolicModel.Helpers ⋯ public

open import SymbolicModel.Strategy ⋯ public
-- open import SymbolicModel.Stripping ⋯ public
