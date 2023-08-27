open import Prelude.Init; open SetAsType
open import Prelude.Lists.Collections
open import Prelude.Lists.Mappings
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.Concat
open import Prelude.Lists.Membership
open import Prelude.Lists.SuffixSubset
open import Prelude.InferenceRules
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Membership

open import Bitcoin using (TxInput′)
open import BitML.BasicTypes using () renaming (⋯ to ⋯′)

module SymbolicModel.Mappings (⋯′ : ⋯′) where

open import Compiler.Mappings ⋯′
open import SymbolicModel.Run ⋯′
  hiding (begin_; _∎)

-- Well-formed terms, where we can provide mappings txout,sechash,κ.
record 𝕎 {X : Type} ⦃ _ : X has Name ⦄ ⦃ _ : X has Ad ⦄ (x : X) : Type where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txout   : Txout   x
    sechash : Sechash x
    κ       : 𝕂²      x

ℝ = Pred₀ Run ∋ 𝕎
module ℝ (𝕣 : ℝ R) where
  open 𝕎 𝕣 public renaming (txout to txout′; sechash to sechash′; κ to κ′)

instance
  ℝ∙Cfg : (ℝ R) ∙Cfg
  ℝ∙Cfg {R = R} = ∙cfg= (const $ R ∙cfg)

ℾᵗ = Pred₀ Cfgᵗ ∋ 𝕎
module ℾᵗ (ℽ : ℾᵗ Γₜ) where
  open 𝕎 ℽ public renaming (txout to txoutΓ; sechash to sechashΓ; κ to κΓ)

ℾᵗ-∅ᵗ : ℾᵗ ∅ᵗ
ℾᵗ-∅ᵗ = record {txout = λ (); sechash = λ (); κ = λ ()}

ℾ = Pred₀ Cfg ∋ 𝕎
module ℾ (ℽ : ℾ Γ) where
  open 𝕎 ℽ public renaming (txout to txoutΓ; sechash to sechashΓ; κ to κΓ)

ℾ-∅ : ℾ ∅ᶜ
ℾ-∅ = record {txout = λ (); sechash = λ (); κ = λ ()}

𝔾 : Pred₀ Ad
𝔾 ad = Valid ad × Txout (ad .G) × Sechash (ad .G) × 𝕂²′ ad

𝕃 : Run → Cfgᵗ → Type
𝕃 R Γₜ = Σ[ 𝕒 ∈ 𝔸 R Γₜ ] ℾᵗ (𝕒 .proj₂ .proj₂ .proj₁)

data ℝ∗ : Run → Type where
  _∎⊣_✓ : ∀ {Γₜ} →

    ∙ ℾᵗ Γₜ
    → (init : Initial Γₜ) →
      ───────────────────
      ℝ∗ (Γₜ ∎⊣ init)

  _∷_⊣_✓ :
    ∀ Γₜ →
    ∙ ℝ∗ R
    → (λˢ : 𝕃 R Γₜ) →
      ───────────────────────
      ℝ∗ (Γₜ ∷ R ⊣ λˢ .proj₁)

ℝ∗-∅ˢ : ℝ∗ ∅ˢ
ℝ∗-∅ˢ = ℾᵗ-∅ᵗ ∎⊣ tt , refl ✓

SRun : Type
SRun = ∃ ℝ∗

-- ** Properties.
Txout≈ : _≈_ ⇒² _→⦅ Txout ⦆_
Txout≈ {Γ}{Γ′} = permute-↦ {P = const TxInput′} ∘ ≈⇒namesʳ↭ {Γ}{Γ′}

Txout≗ : ∀ (Γ≈ : Γ ≈ Γ′) (txoutΓ : Txout Γ) →
  Txout≈ {Γ}{Γ′} Γ≈ txoutΓ ≗⟨ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈ ⟩↦ txoutΓ
Txout≗ {Γ}{Γ′} Γ≈ txoutΓ = permute-≗↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txoutΓ

Sechash≈ : _≈_ ⇒² _→⦅ Sechash ⦆_
Sechash≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒namesˡ↭ {Γ}{Γ′}

Sechash≗ : ∀ (Γ≈ : Γ ≈ Γ′) (sechashΓ : Sechash Γ) →
  Sechash≈ {Γ}{Γ′} Γ≈ sechashΓ ≗⟨ ≈⇒namesˡ↭ {Γ}{Γ′} Γ≈ ⟩↦ sechashΓ
Sechash≗ {Γ}{Γ′} Γ≈ sechashΓ = permute-≗↦ (≈⇒namesˡ↭ {Γ}{Γ′} Γ≈) sechashΓ

𝕂²≈ : _≈_ ⇒² _→⦅ 𝕂² ⦆_
𝕂²≈ {Γ}{Γ′} = permute-↦ ∘ ≈⇒ads↭ {Γ}{Γ′}

𝕂²≗ : ∀ (Γ≈ : Γ ≈ Γ′) (κΓ : 𝕂² Γ) →
  𝕂²≈ {Γ}{Γ′} Γ≈ κΓ ≗⟨ ≈⇒ads↭ {Γ}{Γ′} Γ≈ ⟩↦ κΓ
𝕂²≗ {Γ}{Γ′} Γ≈ κΓ = permute-≗↦ (≈⇒ads↭ {Γ}{Γ′} Γ≈) κΓ

ℾ≈ : Γ ≈ Γ′ → ℾ Γ → ℾ Γ′
ℾ≈ {Γ}{Γ′} Γ≈ ℽ =
  [txout:   Txout≈   {Γ}{Γ′} Γ≈ txoutΓ
  ∣sechash: Sechash≈ {Γ}{Γ′} Γ≈ sechashΓ
  ∣κ:       𝕂²≈      {Γ}{Γ′} Γ≈ κΓ
  ] where open ℾ ℽ

ℾᵗ⇒ℾ : ℾᵗ (Γ at t) → ℾ Γ
ℾᵗ⇒ℾ ℽ = [txout:   txoutΓ
         ∣sechash: sechashΓ
         ∣κ:       κΓ
         ] where open ℾᵗ ℽ

ℾ⇒ℾᵗ : ℾ Γ → ℾᵗ (Γ at t)
ℾ⇒ℾᵗ ℽ = [txout:   txoutΓ
         ∣sechash: sechashΓ
         ∣κ:       κΓ
         ] where open ℾ ℽ

ℾᵗ≈ :  Γₜ ≈ Γₜ′ → ℾᵗ Γₜ → ℾᵗ Γₜ′
ℾᵗ≈ {Γ at t}{Γ′ at .t} (refl , Γ≈) = ℾ⇒ℾᵗ ∘ ℾ≈ Γ≈ ∘ ℾᵗ⇒ℾ

ℝ-∅ˢ : ℝ ∅ˢ
ℝ-∅ˢ = record {txout = λ (); sechash = λ (); κ = λ ()}

𝕃⇒𝔸 : 𝕃 R Γₜ → 𝔸 R Γₜ
𝕃⇒𝔸 = proj₁

𝕃⇒ℾᵗ : 𝕃 R Γₜ → ℾᵗ Γₜ
𝕃⇒ℾᵗ {Γₜ = Γₜ} (𝕒@(α , _ , Γₜ′ , _ , Γ≈ , _) , ℽ) =
  ℾᵗ≈ (≈-sym {x = Γₜ}{Γₜ′} Γ≈) ℽ

𝕃⇒ℾ : 𝕃 R (Γ at t) → ℾ Γ
𝕃⇒ℾ {R} = ℾᵗ⇒ℾ ∘ 𝕃⇒ℾᵗ {R}

ℝ∗⇒ℾᵗ : ℝ∗ R → ℾᵗ (R .end)
ℝ∗⇒ℾᵗ (ℽ ∎⊣ _ ✓) = ℽ
ℝ∗⇒ℾᵗ (_∷_⊣_✓ {R} _ _ λˢ) = 𝕃⇒ℾᵗ {R} λˢ

ℝ∗⇒ℾ : ℝ∗ R → ℾ (R ∙cfg)
ℝ∗⇒ℾ = ℾᵗ⇒ℾ ∘ ℝ∗⇒ℾᵗ

lift_—⟨_⟩—_⊣_ : ∀ {Z A B : Type} {Z′ : Type} {P : Pred₀ Z′}
  → ⦃ _ : A has Z ⦄ → ⦃ _ : B has Z ⦄
  → (a : A) (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′) (b : B)
  → b ≡⦅ f ⦆ a
    --————————————————————————————————————————————————————
  → a →⦅ (λ x → f x ↦′ P) ⦆ b
(lift _ —⟨ _ ⟩— _ ⊣ eq) fa = ⟪ _↦′ _ ⟫ eq ~: fa

lift≗_—⟨_⟩—_⊣_ : ∀ {Z A B : Type} {Z′ : Type} {P : Pred₀ Z′}
  ⦃ _ : A has Z ⦄ → ⦃ _ : B has Z ⦄
  → (a : A) (f : ∀ {X} → ⦃ X has Z ⦄ → X → List Z′) (b : B)
  → (eq : b ≡⦅ f ⦆ a)
  → (mapA : f a ↦′ P)
  → (lift a —⟨ f ⟩— b ⊣ eq) mapA ≗⟨ ↭-reflexive $ sym $ eq ⟩↦ mapA
(lift≗ _ —⟨ _ ⟩— _ ⊣ eq) _ _ rewrite eq = refl

Txout∈ : Txout R → Γ ∈ allCfgs R → Txout Γ
Txout∈ txout Γ∈
  = txout
  ∘ mapMaybe-⊆ isInj₂ (⊆-concat⁺ (L.Mem.∈-map⁺ collect Γ∈))

Sechash∈ : Sechash R → Γ ∈ allCfgs R → Sechash Γ
Sechash∈ sechash Γ∈
  = sechash
  ∘ mapMaybe-⊆ isInj₁ (⊆-concat⁺ (L.Mem.∈-map⁺ collect Γ∈))

txout∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → Txout Γₜ′
  → Txout R
  → Txout (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
txout∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) txoutΓ′ txoutR
  = subst (_↦ TxInput′) (sym $ namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq)
  $ txoutR ++/↦ Txout≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) txoutΓ′

sechash∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → Sechash Γₜ′
  → Sechash R
  → Sechash (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
sechash∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R}
  Γ→ eq@((_ , Γ≈) , _) sechashˡ sechashʳ
  rewrite namesˡ-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
        = sechashʳ ++/↦ (Sechash≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) sechashˡ)

κ∷ : (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → 𝕂² Γₜ′
  → 𝕂² R
  → 𝕂² (Γₜ″ ⟨ Γ→ ⟩←—— R ⊣ eq)
κ∷ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R} Γ→ eq@((_ , Γ≈) , _) κˡ κʳ
  rewrite ads-←—— {Γₜ = Γₜ″} {R = R} Γ→ eq
        = κʳ ++/↦ (𝕂²≈ {x = cfg Γₜ′}{cfg Γₜ″} (↭-sym Γ≈) κˡ)

ℝ-base : ∀ {init : Initial Γₜ}
  → ℾᵗ Γₜ
  → ℝ (Γₜ ∎⊣ init)
ℝ-base {init = i} ℽ =
  [txout:   substʳ (_↦ TxInput′) (namesʳ-∎ {init = i}) txoutΓ
  ∣sechash: substʳ (_↦ ℤ)        (namesˡ-∎ {init = i}) sechashΓ
  ∣κ:       substʳ (_↦′ 𝕂²′)     (ads-∎    {init = i}) κΓ
  ] where open ℾᵗ ℽ

ℝ-step : ℝ R → (λˢ : 𝕃 R Γₜ) → ℝ (Γₜ ∷ R ⊣ λˢ .proj₁)
ℝ-step {R = R} 𝕣 ((_ , _ , _ , Γ→ , eq) , ℽ) =
  [txout:   txout∷   {R = R} Γ→ eq txoutΓ    txout′
  ∣sechash: sechash∷ {R = R} Γ→ eq sechashΓ  sechash′
  ∣κ:       κ∷       {R = R} Γ→ eq κΓ        κ′
  ] where open ℝ 𝕣; open ℾᵗ ℽ

ℝ∗⇒ℝ : ℝ∗ ⊆¹ ℝ
ℝ∗⇒ℝ {R} = λ where
  (ℽ ∎⊣ init ✓)  → ℝ-base {init = init} ℽ
  (_ ∷ 𝕣 ⊣ λˢ ✓) → ℝ-step (ℝ∗⇒ℝ 𝕣) λˢ

txout∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ Txout ⦆ Rˢ
txout∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) txout′ =
  destruct≡-++/↦ {zs = namesʳ (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (namesʳ-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    txout′ .proj₁

sechash∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ Sechash ⦆ Rˢ
sechash∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) sechash′ =
  destruct≡-++/↦ {zs = namesˡ (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (namesˡ-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    sechash′ .proj₁

κ∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ 𝕂² ⦆ Rˢ
κ∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) κ′ =
  destruct≡-++/↦ {zs = advertisements (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (ads-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    κ′ .proj₁

drop-ℝ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) → ℝ (Γₜ ∷ Rˢ ⊣ 𝕒) → ℝ Rˢ
drop-ℝ {Rˢ = Rˢ} 𝕒 𝕣′ =
  [txout:   txout∷˘   {Rˢ = Rˢ} 𝕒 txout′
  ∣sechash: sechash∷˘ {Rˢ = Rˢ} 𝕒 sechash′
  ∣κ:       κ∷˘       {Rˢ = Rˢ} 𝕒 κ′
  ] where open ℝ 𝕣′

Last∈-end∈allCfgsᵗ : ∀ R → Last∈ (end∈allCfgsᵗ R)
Last∈-end∈allCfgsᵗ R = go (R ∙trace′)
  where
    go : ∀ (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Last∈ (⟫end∈allCfgsᵗ.go tr)
    go = λ where
      (_ ∎ₜ)               → refl
      (_ —→ₜ⟨ _ ⟩ _ ⊢ tr′) → go tr′

ℝ⊆ : (xy∈ : (Γₜ , Γₜ′) ⋯∈ᵗ R) → ℝ R → ℝ (splitRunˡ R xy∈)
ℝ⊆ {R = R} xy∈ᵗ 𝕣 =
  let
    open ℝ 𝕣
    tr  = R ∙trace′
    R′  = splitRunˡ R xy∈ᵗ
    tr′ = R′ ∙trace′
    tr⊆ = ⊆ˢ-splitTraceˡ tr xy∈ᵗ

    Txout⊆ : R →⦅ Txout ⦆ R′
    Txout⊆ txoutR = txoutR ∘ mapMaybe-⊆ isInj₂ (⊆ˢ⇒names⊆ tr′ tr tr⊆)

    Sechash⊆ : R →⦅ Sechash ⦆ R′
    Sechash⊆ sechashR = sechashR ∘ mapMaybe-⊆ isInj₁ (⊆ˢ⇒names⊆ tr′ tr tr⊆)

    𝕂⊆ : R →⦅ 𝕂² ⦆ R′
    𝕂⊆ κ = κ ∘ (⊆ˢ⇒ads⊆ tr′ tr tr⊆)
  in
    [txout:   Txout⊆ txout′
    ∣sechash: Sechash⊆ sechash′
    ∣κ:       𝕂⊆ κ′
    ]

-- lifting mappings from last configuration to enclosing runs
-- i.e. Γ →⦅ Txout ⟩ Γ′ ———→ R ⇒⟨ Txout ⦆ R′
LIFTˢ : ∀ {R}{t}{t′} (r : ℝ R) Γ (R≈ : R ≈⋯ Γ at t) Γ′ →
  ∙ Γ →⦅ Txout ⦆ Γ′
  ∙ Γ →⦅ Sechash ⦆ Γ′
  ∙ Γ →⦅ 𝕂² ⦆ Γ′
    ────────────────────────
    ℾᵗ (Γ′ at t′)
LIFTˢ {R} r Γ (_ , Γ≈) Γ′ txout↝ sechash↝ κ↝
  = [txout: txoutΓ′ ∣sechash: sechashΓ′ ∣κ: κΓ′ ]
  where
    open ℝ r

    txoutΓ′ : Txout Γ′
    txoutΓ′ = txout↝ $ Txout≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)

    -- pv↝ :
    --   ∙ ValuePreserving  {Γ} txout′
    --   ∙ ValuePreserving↝ {Γ}{Γ′} txout↝
    --     ──────────────────────────────────
    --     ValuePreserving txoutΓ′
    -- pv↝ pv pvΓ
    --   = pvΓ (Txout≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R))
    --   ∘ ValuePreserving-Txout≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ txout′ $ namesʳ⦅end⦆⊆ R)
    --   ∘ {!!}

    sechashΓ′ : Sechash Γ′
    sechashΓ′ = sechash↝ $ Sechash≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ sechash′ $ namesˡ⦅end⦆⊆ R)

    κΓ′ : 𝕂² Γ′
    κΓ′ = κ↝ (𝕂²≈ {R ∙cfg}{Γ} Γ≈ (weaken-↦ κ′ $ ads⦅end⦆⊆ R))

module _ {R} (𝕣 : ℝ R) where
  _∙txout_ = 𝕣 .ℝ.txout′

  _∙txoutEnd_ : Txout (R .end)
  _∙txoutEnd_ = _∙txout_ ∘ namesʳ⦅end⦆⊆ R

  _∙txoutΓ_ : ∀ {Γ} → (R ≈⋯ Γ at t) × (x ∈ namesʳ Γ) → TxInput′
  _∙txoutΓ_ {Γ = Γ} (R≈@(_ , Γ≈) , x∈) = Txout≈ {R .end .cfg}{Γ} Γ≈ _∙txoutEnd_ x∈

  _∙txoutΓ⟨_⟩_ : ∀ Γ → (R ≈⋯ Γ at t) × (x ∈ namesʳ Γ) → TxInput′
  _∙txoutΓ⟨_⟩_ Γ (R≈@(_ , Γ≈) , x∈) = Txout≈ {R .end .cfg}{Γ} Γ≈ _∙txoutEnd_ x∈

  _∙txoutC_ : ∀ {c v x} → R ≈⋯ ⟨ c , v ⟩at x ⋯ → TxInput′
  _∙txoutC_ = _∙txoutEnd_ ∘ c∈⇒x∈ (R ∙cfg)

-- ** Meta-properties.

Suffix⊆-subst : ∀ {X : Type ℓ} {xs ys zs : List X} (eq : ys ≡ zs) (xs⊆ : xs ⊆ ys)
  → Suffix⊆ xs⊆
  → Suffix⊆ (subst (_ L.Mem.∈_) eq ∘ xs⊆)
Suffix⊆-subst refl _ p = p

txout∷∘namesʳ⦅end⦆⊆ : (Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′) (eq : Γₜ″ ≈ Γₜ′ × R .end ≈ Γₜ)
  → let R′ = Γₜ″ ⟨ Γ→Γ′ ⟩←—— R ⊣ eq in
  (txoutΓ′ : Txout Γₜ′)
  (txoutR : Txout R)
  → ∀ {x : Id} (x∈ : x ∈ namesʳ Γₜ″)
  --————————————————————————
  → (txout∷ {R = R} Γ→Γ′ eq txoutΓ′ txoutR) (namesʳ⦅end⦆⊆ R′ x∈)
  ≡ Txout≈ {Γₜ′ .cfg}{Γₜ″ .cfg} (↭-sym $ eq .proj₁ .proj₂) txoutΓ′ x∈
txout∷∘namesʳ⦅end⦆⊆ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} {Γₜ″ = Γₜ″} {R = R}
  Γ→Γ′ eq@((_ , Γ≈) , _) txoutΓ′ txoutR {x} x∈
  = ++/↦≡-inj₂ n≡ _ _ _ _ is-inj₂
  where
    _R′ = Γₜ″ ⟨ Γ→Γ′ ⟩←—— R ⊣ eq

    n≡ : namesʳ _R′ ≡ namesʳ R ++ namesʳ Γₜ″
    n≡ = namesʳ-←—— {Γₜ = Γₜ″} {R = R} Γ→Γ′ eq

    x∈₁ : x ∈ namesʳ _R′
    x∈₁ = namesʳ⦅end⦆⊆ _R′ x∈

    x∈₂ : x ∈ namesʳ R ++ namesʳ Γₜ″
    x∈₂ = subst (x L.Mem.∈_) n≡ x∈₁

    n⊆₀ : names Γₜ″ ⊆ names _R′
    n⊆₀ = ⊆-concat⁺ $ L.Mem.∈-map⁺ names $ L.Mem.∈-map⁺ cfg $ end∈allCfgsᵗ _R′

    n⊆₁ : namesʳ Γₜ″ ⊆ namesʳ _R′
    n⊆₁ = mapMaybe-⊆ isInj₂ n⊆₀

    n⊆ : namesʳ Γₜ″ ⊆ namesʳ R ++ namesʳ Γₜ″
    n⊆ = subst (_ L.Mem.∈_) n≡ ∘ n⊆₁

    suffix-n⊆ : Suffix⊆ n⊆
    suffix-n⊆
      = Suffix⊆-subst n≡ n⊆₁
      $ Suffix⊆-mapMaybe isInj₂ n⊆₀
      $ Last∈-concat (L.Mem.∈-map⁺ names $ L.Mem.∈-map⁺ cfg $ end∈allCfgsᵗ _R′)
      $ Last∈-map⁺ names (L.Mem.∈-map⁺ cfg $ end∈allCfgsᵗ _R′)
      $ Last∈-map⁺ cfg (end∈allCfgsᵗ _R′)
      $ Last∈-end∈allCfgsᵗ _R′

    is-inj₂ : L.Mem.∈-++⁻ (namesʳ R) {namesʳ Γₜ″} x∈₂ ≡ inj₂ x∈
    is-inj₂ = Suffix⊆-++⁻ _ _ suffix-n⊆

Txout≈∘Txout≈⁻¹ : ∀ {Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′) (txout : Txout Γ)
  → Txout≈ {Γ′}{Γ} (↭-sym Γ≈) (Txout≈ {Γ}{Γ′} Γ≈ txout) ≗↦ txout
Txout≈∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txout {x} x∈ =
  begin
    ( Txout≈ {Γ′}{Γ} (↭-sym Γ≈)
    $ Txout≈ {Γ}{Γ′} Γ≈ txout
    ) x∈
  ≡⟨⟩
    ( permute-↦ (≈⇒namesʳ↭ {Γ′}{Γ} $ ↭-sym Γ≈)
    $ Txout≈ {Γ}{Γ′} Γ≈ txout
    ) x∈
  ≡⟨⟩
    ( permute-↦ (≈⇒namesʳ↭ {Γ′}{Γ} $ ↭-sym Γ≈)
    $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout
    ) x∈
  ≡⟨ cong (λ ◆ → (permute-↦ ◆ $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout) x∈)
          (sym $ ↭-sym∘≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) ⟩
    ( permute-↦ (↭-sym $ ≈⇒namesʳ↭ {Γ}{Γ′} Γ≈)
    $ permute-↦ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout
    ) x∈
  ≡⟨ permute-↦∘permute-↦˘ (≈⇒namesʳ↭ {Γ}{Γ′} Γ≈) txout x∈ ⟩
    txout x∈
  ∎ where open ≡-Reasoning

-- Txout≈∘lift∘Txout≈⁻¹ : ∀ {Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′) (txout : Txout Γ)
--   (namesʳ≡ : Γ′ ≡⦅ namesʳ ⦆ Γ″)
--   → ( Txout≈ {Γ″}{Γ} (↭-sym Γ≈)
--     $ (lift Γ′ —⟨ namesʳ ⟩— Γ″ ⊣ namesʳ≡)
--     $ Txout≈ {Γ}{Γ′} Γ≈ txout
--     )
--   ≗↦ txout
-- Txout≈∘lift∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txout {x} x∈ =

++/↦-Txout≈∘Txout≈⁻¹ : ∀ {Γ₀ Γ Γ′ : Cfg} (Γ≈ : Γ ≈ Γ′)
  (txoutˡ : Txout Γ₀)
  (txoutʳ : Txout Γ)
  →  (txoutˡ ++/↦ (Txout≈ {Γ′}{Γ} (↭-sym Γ≈) $ Txout≈ {Γ}{Γ′} Γ≈ txoutʳ))
  ≗↦ (txoutˡ ++/↦ txoutʳ)
++/↦-Txout≈∘Txout≈⁻¹ {Γ₀}{Γ}{Γ′} Γ≈ txoutˡ txoutʳ {x} x∈
  with L.Mem.∈-++⁻ (namesʳ Γ₀) x∈
... | inj₁ _  = refl
... | inj₂ y∈ = Txout≈∘Txout≈⁻¹ {Γ}{Γ′} Γ≈ txoutʳ y∈
