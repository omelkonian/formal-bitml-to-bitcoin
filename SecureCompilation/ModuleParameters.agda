module SecureCompilation.ModuleParameters where

open import Prelude.Init; open SetAsType
open import Prelude.Lists.Finite

open import Bitcoin.Crypto using (KeyPair)
import BitML.BasicTypes as BitML

record ⋯ : Type₁ where
  constructor ⋯_,_,_,_⋯
  -- ** BitML parameters
  field ⋯′ : BitML.⋯
  open BitML.⋯ ⋯′ public

  -- ** Compiler parameters
  field η : ℕ -- security parameters for hash lengths

  -- ** Secure compilation parameters
  field finPart : Finite Participant
        keypairs : Participant → KeyPair × KeyPair

open ⋯ public
