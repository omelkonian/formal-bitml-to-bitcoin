open import Prelude.Init

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation (⋯ : ⋯) (let open ⋯ ⋯) where

open import SecureCompilation.Parsing ⋯ public
-- [WIP]
open import SecureCompilation.Backtranslation.Unparsing
open import SecureCompilation.Backtranslation ⋯ public
open import SecureCompilation.ComputationalSoundness ⋯ public
