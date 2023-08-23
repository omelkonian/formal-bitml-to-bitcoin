module ComputationalModel.Serialization where

open import Prelude.Init; open SetAsType
open import Prelude.Newtype

open import Bitcoin
open import Prelude.Serializable HashId public

private variable
  X : Type ℓ; Y : Type ℓ′; P : X → Type ℓ′
  A B : Type
  x : X; y : Y
  k k′ : KeyPair

postulate instance
  Serializable-⊎ : ⦃ Serializable X ⦄ → ⦃ Serializable Y ⦄ → Serializable (X ⊎ Y)
  Serializable-Σ : ⦃ Serializable X ⦄ → ⦃ ∀ {x} → Serializable (P x) ⦄ →
    Serializable (Σ X P)
  Serializable-List : ⦃ Serializable X ⦄ → Serializable (List X)

  Serialiazable-String : Serializable String
  Serializable-ℕ       : Serializable ℕ
  Serializable-Bool    : Serializable Bool
  Serializable-ℤ       : Serializable ℤ
  Serialiazable-Tx     : Serializable (Tx i o)

private
  _ = Serializable ∃Tx    ∋ it
  _ = Serializable HashId ∋ it

_≢′_ : ∀ {A : Type ℓ} → Rel A _
_≢′_ = newtype² _≢_

postulate
  -- signing with different keys never collides
  SIG≢ : ⦃ k ≢′ k′ ⦄ → SIG k x ≢ SIG k′ y

  -- encodings of different values of different types never collide
  encode≢ : ⦃ _ : Serializable A ⦄ ⦃ _ : Serializable B ⦄ {a : A} {b : B} →
    ⦃ A ≢′ B ⦄ → encode a ≢ encode b

  SIG≢encode : ∀ ⦃ _ : Serializable B ⦄ {k} {x : A} {y : B} →
    SIG k x ≢ encode y
