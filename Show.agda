open import Prelude.Semigroup
open import Prelude.Show

instance
  Show-↦ : ∀ {A : Type ℓ} {B : A → Type ℓ′} {xs : List A} →
    ⦃ Show A ⦄ → ⦃ ∀ {x} → Show (B x) ⦄ → Show (xs ↦′ B)
  Show-↦ {xs = xs} .show f = show $ mapWith∈ xs λ {x} x∈ →
    parens $ show x ◇ " , " ◇ show (f x∈)
  -- zip (dom f) (codom f)

  -- Show-↦ : ∀ {A : Type ℓ} {B : A → Type ℓ′} {xs : List A} →
  --   ⦃ Show A ⦄ → ⦃ ∀ {x} → Show (B x) ⦄ → Show (∀ {x} → x ∈ xs → B x)
  -- Show-↦ {xs = xs} .show f = show $ mapWith∈ xs λ {x} x∈ →
  --   parens $ show x ◇ " , " ◇ show (f x∈)

  Show-ℤ : Show ℤ
  Show-ℤ .show = Sh.show
    where import Data.Integer.Show as Sh

  Show-KeyPair : Show KeyPair
  Show-KeyPair .show k =
    "keys: {pub ↦ " ◇ show (k .pub) ◇ ", sec ↦ " ◇ show (k .sec) ◇ "}"

  Show-D : Show Branch
  Show-D .show _ = "D"

  -- Show-Ad : Show Ad
  -- Show-Ad .show _ = "⟨G⟩C"

  Show-Part : Show Participant
  Show-Part .show = λ where
    A → "A"
    B → "B"

  Show-Tx∃Tx : Show ∃Tx
  Show-Tx∃Tx .show (i , o , _) = parens (show i) ◇ "↝tx↝" ◇ parens (show o)

  Show-TxInput′ : Show TxInput′
  Show-TxInput′ .show (tx at i) = show tx ◇ " at " ◇ show i

  -- Show-Txout : ∀ {X : Type} {x : X} ⦃ _ : X has Name ⦄ → Show (Txout x)
  -- Show-Txout {x = x} .show txout = show $ mapWith∈ (ids x) λ {i} i∈ →
  --   parens $ show i ◇ " , " ◇ show (txout i∈)

  -- Show-Sechash : ∀ {X : Type} {x : X} ⦃ _ : X has Name ⦄ → Show (Txout x)
  -- Show-Sechash {x = x} .show txout = show $ mapWith∈ (ids x) λ {i} i∈ →
  --   parens $ show i ◇ " , " ◇ show (txout i∈)

  Show-𝔾 : Show (𝔾 ad)
  Show-𝔾 {ad} .show (vad , txout , sechash , K) =
        "∙ valid: ✓"
    ◇ "\n∙ txout: " ◇ show ⦃ Show-↦ ⦄ txout
    -- show ⦃ Show-Txout {x = ad .Ad.G} ⦄ txout -- show txout
    ◇ "\n∙ sechash:" ◇ show ⦃ Show-↦ ⦄ sechash
    ◇ "\n∙ K:" ◇ show ⦃ Show-↦ ⦄ K
