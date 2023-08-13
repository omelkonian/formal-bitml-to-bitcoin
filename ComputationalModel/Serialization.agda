module ComputationalModel.Serialization where

open import Prelude.Init

open import Bitcoin using (HashId)
open import Prelude.Serializable HashId public

private variable X : Set ℓ; Y : Set ℓ′

instance postulate
  Serializable-ℕ : Serializable ℕ
  Serializable-ℤ : Serializable ℤ
  Serializable-Bool : Serializable Bool
  Serializable-List : ⦃ Serializable X ⦄ → Serializable (List X)
  Serializable-× : ⦃ Serializable X ⦄ → ⦃ Serializable Y ⦄ → Serializable (X × Y)
  Serializable-⊎ : ⦃ Serializable X ⦄ → ⦃ Serializable Y ⦄ → Serializable (X ⊎ Y)
