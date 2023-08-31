open import Prelude.Init

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation (⋯ : ⋯) (let open ⋯ ⋯) where

open import SecureCompilation.Parsing ⋯ public
open import SecureCompilation.Unparsing ⋯ public
open import SecureCompilation.StrategyTranslation ⋯ public
open import SecureCompilation.ComputationalSoundness ⋯ public
