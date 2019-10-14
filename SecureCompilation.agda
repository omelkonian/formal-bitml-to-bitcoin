open import Level using (0ℓ)

open import Data.Nat     using (ℕ; _>_)
open import Data.List    using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)

open import Relation.Binary  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Hashing.Base

module SecureCompilation -- (see BitML paper, Section 7)
  -- UTxO parameters
  (Address : Set)
  (_♯ₐ : Hash Address)
  (_≟ₐ_ : Decidable {A = Address} _≡_)

  -- BitML parameters
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

-- UTxO
open import UTxO.Ledger Address _♯ₐ _≟ₐ_ using (Tx; Ledger)

-- BitML
open import Types       Participant _≟ₚ_ Honest using (Value; Values)
open import BitML.Types Participant _≟ₚ_ Honest using (Contracts; Advertisement; ⟨_⟩_∶-_)

variable
  v : Value
  vs vsᶜ vsᵛ vsᵖ : Values
  c : Contracts v vs
  ad : Advertisement v vsᶜ vsᵛ vsᵖ

bitml-compiler : Advertisement v vsᶜ vsᵛ vsᵖ → List Tx
bitml-compiler (⟨ G ⟩ C ∶- _) = {!!}
