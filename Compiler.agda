open import Prelude.Init; open SetAsType

open import BitML.BasicTypes using (⋯)

module Compiler (⋯ : ⋯) (η : ℕ) where

open import Compiler.Mappings ⋯ public
open import Compiler.Outputs ⋯ public
open import Compiler.Translation ⋯ η public
