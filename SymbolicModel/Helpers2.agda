open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-trans)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open L.Mem using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.DecLists
open import Prelude.Setoid

open import Bitcoin.Crypto
open import Bitcoin.Tx

module SymbolicModel.Helpers2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run2 Participant Honest
  hiding ( _∎; begin_
         ; {-variables-} g; c; as; vs; xs; ad; Γ; Γ′; R′; Δ )
open import SymbolicModel.Collections2 Participant Honest

-- Useful type aliases for maps over specific sets.
private variable X : Set

Txout : ⦃ _ : X has Name ⦄ → Pred₀ X
Txout x = namesʳ x ↦ TxInput′

Sechash : ⦃ _ : X has Name ⦄ → Pred₀ X
Sechash x = namesˡ x ↦ ℤ

𝕂 : Pred₀ Precondition
𝕂 g = nub-participants g ↦ KeyPair

𝕂²′ : Pred₀ Advertisement
𝕂²′ (⟨ g ⟩ c) = subtermsᶜ′ c ↦ nub-participants g ↦ KeyPair

𝕂² : ⦃ _ : X has Advertisement ⦄ → Pred₀ X
𝕂² x = advertisements x ↦′ 𝕂²′

----

_≡⟨on:_⟩_ : ∀ {X : Set} → Configuration → (Configuration → X) → Configuration → Set
Γ ≡⟨on: f ⟩ Γ′ = f Γ ≡ f Γ′

_⊆⟨on:_⟩_ : ∀ {Z A B : Set} ⦃ _ : A has Z ⦄ ⦃ _ : B has Z ⦄ → A → (∀ {X} ⦃ _ : X has Z ⦄ → X → List Z) → B → Set
a ⊆⟨on: f ⟩ b = f a ⊆ f b

-- [BUG] cannot use names⊆ as an index, need to partially apply the module and apply names⊆ everytime :(
-- [WORKAROUND] Expose instantiated operator to help Agda's inference
_⊆⟨on:names⟩_ : Precondition → Configuration → Set
_⊆⟨on:names⟩_ = _⊆⟨on: names ⟩_

_↝⟨_⟩_ : ∀ {Z A B : Set} ⦃ _ : A has Z ⦄ ⦃ _ : B has Z ⦄ → A → (F : ∀ {X} ⦃ _ : X has Z ⦄ → Pred₀ X) → B → Set
A ↝⟨ F ⟩ A′ = F A → F A′

liftʳ : ∀ {Γ Γ′}
  → Γ′ ≡⟨on: namesʳ ⟩ Γ
  → Γ  ↝⟨ Txout     ⟩ Γ′
liftʳ eq txout′ rewrite eq = txout′

liftˡ : ∀ {Γ Γ′}
  → Γ′ ≡⟨on: namesˡ ⟩ Γ
  → Γ  ↝⟨ Sechash   ⟩ Γ′
liftˡ eq sechash′ rewrite eq = sechash′

liftᵃ : ∀ {Γ Γ′}
  → Γ′ ≡⟨on: advertisements ⟩ Γ
  → Γ  ↝⟨ 𝕂²                 ⟩ Γ′
liftᵃ eq κ′ rewrite eq = κ′

-- --

deposit∈Γ⇒namesʳ : ∀ {Γ}
  → ⟨ A has v ⟩at x ∈ᶜ Γ
  → x ∈ namesʳ Γ
deposit∈Γ⇒namesʳ {A} {v} {x} {` _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ , _ ⟩at _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ has _ ⟩at .x} (here refl) = here refl
deposit∈Γ⇒namesʳ {A} {v} {x} {_ auth[ _ ]} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {⟨ _ ∶ _ ♯ _ ⟩} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {_ ∶ _ ♯ _} (here ())
deposit∈Γ⇒namesʳ {A} {v} {x} {l ∣ r} d∈
  rewrite mapMaybe-++ isInj₂ (names l) (names r)
  with L.Mem.∈-++⁻ (cfgToList l) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ   $ deposit∈Γ⇒namesʳ {Γ = l} d∈ˡ
... | inj₂ d∈ʳ = ∈-++⁺ʳ _ $ deposit∈Γ⇒namesʳ {Γ = r} d∈ʳ

deposit∈R⇒namesʳ : ⟨ A has v ⟩at x ∈ᶜ cfg (R .end) → x ∈ namesʳ R
deposit∈R⇒namesʳ {R = R} = deposit∈Γ⇒namesʳ {Γ = cfg (R .end)}

--

-- [BUG] somehow if we didn't package this constructor arguments in ℝ, we get unification/panic errors!
-- (issue appear at the usage site)
-- ℝ = ∃[ R ] (Txout R × Sechash R × 𝕂² R)
record ℝ (R : Run) : Set where
  constructor [txout:_∣sechash:_∣κ:_]
  field
    txout′   : Txout R
    sechash′ : Sechash R
    κ′       : 𝕂² R

-- lifting mappings from last configuration to enclosing runs
-- e.g. Γ ↝⟨ Txout ⟩ Γ′ ———→ R ↝⟨ Txout ⟩ R′

≈ᵗ-refl : Γₜ ≈ Γₜ
≈ᵗ-refl = refl , ↭-refl

module Lift (r : ℝ R) t α t′
  Γ (cfg≡ : R ≡⋯ Γ at t) Γ′
  (valid↝   : Γ at t —[ α ]→ₜ Γ′ at t′)
  (txout↝   : Γ ↝⟨ Txout   ⟩ Γ′)
  (sechash↝ : Γ ↝⟨ Sechash ⟩ Γ′)
  (κ↝       : Γ ↝⟨ 𝕂²      ⟩ Γ′)
  where
  open ℝ r

  private
    Γ≡ = cong cfg cfg≡

    R≈ : (Γ′ at t′ ≈ Γ′ at t′) × (R .end ≈ Γ at t)
    R≈ rewrite cfg≡ = ≈ᵗ-refl {Γ′ at t′} , ≈ᵗ-refl {Γ at t}

    R′ = (Γ′ at t′) ⟨ valid↝ ⟩←—— R ⊣ R≈

  txout : Txout R′
  txout = txout↝ $ subst Txout Γ≡ txout′

  sechash : Sechash R′
  sechash = sechash↝ $ subst Sechash Γ≡ sechash′

  κ : 𝕂² R′
  κ {ad} ad∈ with ads∈-⊎ {α}{Γ′ at t′}{Γ′ at t′}{R}{ad}{Γ at t} valid↝ R≈ ad∈
  ... | inj₁ ad∈R  = κ′ ad∈R
  ... | inj₂ ad∈Γ′ = κ↝ (subst 𝕂² Γ≡ (weaken-↦ κ′ (ads⦅end⦆⊆ {R}))) ad∈Γ′

  𝕣′ : ℝ R′
  𝕣′ = [txout: txout ∣sechash: sechash ∣κ: κ ]

-- invoking the compiler with the correct mappings, lifting them from the current configuration/run
-- e.g. (Txout R ∣ Γ ↝⟨ Txout ⟩ G) ———→ Txout G
module Lift₀ (r : ℝ R) (t : Time)
  Γ (cfg≡ : R ≡⋯ Γ at t) ad
  (txout↝   : Γ ↝⟨ Txout   ⟩ G ad)
  (sechash↝ : Γ ↝⟨ Sechash ⟩ G ad)
  (ad∈ : ad ∈ advertisements R)
  where
  open ℝ r

  private Γ≡ = cong cfg cfg≡

  txout₀ : Txout (G ad)
  txout₀ = txout↝ $ subst Txout Γ≡ txout′

  sechash₀ : Sechash (G ad)
  sechash₀ = sechash↝ $ subst Sechash Γ≡ sechash′

  κ₀ : 𝕂²′ ad
  κ₀ = κ′ ad∈

--- ** name helpers

namesʳ-∥map-helper : ∀ (ds : List (Participant × Value × Id))
  → map (proj₂ ∘ proj₂) ds
  ⊆ namesʳ (|| map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds)
namesʳ-∥map-helper (_ ∷ []) (here refl) = here refl
namesʳ-∥map-helper (_ ∷ _ ∷ _) (here refl) = here refl
namesʳ-∥map-helper ((Bᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) (there d∈) = there $ (namesʳ-∥map-helper ds) d∈

n≡ : ∀ {A : Set} {P Q : A → Configuration}
  → (∀ x → Null $ namesʳ (Q x) )
  → (xs : List A)
  → namesʳ (|| map (λ x → P x ∣ Q x) xs)
  ≡ namesʳ (|| map P xs)
n≡ ∀x [] = refl
n≡ {P = P}{Q} ∀x (x₁ ∷ []) = P∣Q≡
  where
    P∣Q≡ : namesʳ (P x₁ ∣ Q x₁) ≡ namesʳ (P x₁)
    P∣Q≡ rewrite mapMaybe-++ isInj₂ (names $ P x₁) (names $ Q x₁) | ∀x x₁ | L.++-identityʳ (namesʳ $ P x₁) = refl
n≡ {P = P}{Q} ∀x (x₁ ∷ xs@(_ ∷ _)) =
  begin
    namesʳ (|| (P x₁ ∣ Q x₁ ∷ map (λ x → P x ∣ Q x) xs))
  ≡⟨⟩
    namesʳ (P x₁ ∣ Q x₁ ∣ || map (λ x → P x ∣ Q x) xs)
  ≡⟨ mapMaybe-++ isInj₂ (names $ P x₁ ∣ Q x₁) (names $ || map (λ x → P x ∣ Q x) xs) ⟩
    namesʳ (P x₁ ∣ Q x₁) ++ namesʳ (|| map (λ x → P x ∣ Q x) xs)
  ≡⟨ cong (_++ namesʳ (|| map (λ x → P x ∣ Q x) xs)) P∣Q≡ ⟩
    namesʳ (P x₁) ++ namesʳ (|| map (λ x → P x ∣ Q x) xs)
  ≡⟨ cong (namesʳ (P x₁) ++_) rec ⟩
    namesʳ (P x₁) ++ namesʳ (|| map P xs)
  ≡⟨ (sym $ mapMaybe-++ isInj₂ (names $ P x₁) (names $ || map P xs)) ⟩
    namesʳ (|| (P x₁ ∷ map P xs))
  ∎
  where
    open ≡-Reasoning

    P∣Q≡ : namesʳ (P x₁ ∣ Q x₁) ≡ namesʳ (P x₁)
    P∣Q≡ rewrite mapMaybe-++ isInj₂ (names $ P x₁) (names $ Q x₁) | ∀x x₁ | L.++-identityʳ (namesʳ $ P x₁) = refl

    rec : namesʳ (|| map (λ x → P x ∣ Q x) xs) ≡ namesʳ (|| map P xs)
    rec = n≡ {P = P}{Q} ∀x xs

namesʳ-∥map-helper′ : ∀ (ds : List (Participant × Value × Id)) → let xs = map (proj₂ ∘ proj₂) ds in
      xs ⊆ namesʳ (|| map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds))
namesʳ-∥map-helper′ {y = y} ds {x} x∈ = qed
  where
    PVI = Participant × Value × Id
    x̂ = map (proj₂ ∘ proj₂) ds
    eds = enumerate ds

    P : PVI → Configuration
    P (Aᵢ , vᵢ , xᵢ) = ⟨ Aᵢ has vᵢ ⟩at xᵢ

    P′ : ∀ {A : Set} → A × PVI → Configuration
    P′ = P ∘ proj₂

    Q P∣Q : Index ds × PVI → Configuration
    Q (i , Aᵢ , vᵢ , xᵢ) = Aᵢ auth[ x̂ , ‼-map {xs = ds} i ▷ᵈˢ y ]
    P∣Q x = P′ x ∣ Q x

    h : namesʳ (|| map P∣Q eds)
      ≡ namesʳ (|| map P′ eds)
    h = n≡ {A = Index ds × PVI} {P = P′} {Q = Q} (λ _ → refl) eds

    -- [BUG] if I replace `enumerate ds` with `eds` I get an error!?
    h′ : ∀ (ds : List PVI) → map P′ (enumerate ds) ≡ map P ds
    h′ [] = refl
    h′ (pvi ∷ ds) = cong (_ ∷_) qed
      where
        rec : map P′ (zip (L.tabulate {n = length ds} (fsuc ∘ id)) ds)
            ≡ map (P′ ∘ map₁ fsuc) (zip (L.tabulate {n = length ds} id) ds)
        rec = map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate {m = length ds} ds {P = P′} {f = id}

        qed : map P′ (zip (L.tabulate {n = length ds} fsuc) ds)
            ≡ map P ds
        qed = trans rec (h′ ds)

    qed : x ∈ namesʳ (|| map P∣Q eds)
    qed rewrite h | h′ ds = namesʳ-∥map-helper ds x∈
    -- qed = subst (x L.Mem.∈_) (sym h) (subst (λ ◆ → x L.Mem.∈ namesʳ (|| ◆)) (sym $ h′ ds) (namesʳ-∥map-helper ds x∈))

--

module _ (𝕣 : ℝ R) (t : Time) (α : Label) (t′ : Time) where
  open ℝ 𝕣

  module _ Γ (cfg≡ : R ≡⋯ Γ at t) ad where
    private
      Γ′ = ` ad ∣ Γ
    module H₁ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public

  module _ Γ (cfg≡ : R ≡⋯ Γ at t) B A ad (Δ : List (Secret × Maybe ℕ)) where
    private
      Γ′ = Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ]
      as = proj₁ $ unzip Δ
    module H₂ (sechash⁺ : proj₁ (unzip Δ) ↦ ℤ) (k⃗ : 𝕂²′ ad) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      private
        hʳ : ∀ Δ → Null $ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        hʳ [] = refl
        hʳ (_ ∷ []) = refl
        hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _

        hˡ : ∀ Δ → namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) ≡ proj₁ (unzip Δ)
        hˡ [] = refl
        hˡ (_ ∷ []) = refl
        hˡ ((s , m) ∷ Δ@(_ ∷ _)) =
          begin
            namesˡ (⟨ B ∶ s ♯ m ⟩ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨ mapMaybe-++ isInj₁ (names ⟨ B ∶ s ♯ m ⟩) (names $ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
            namesˡ ⟨ B ∶ s ♯ m ⟩ ++ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨⟩
            s ∷ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
          ≡⟨ cong (s ∷_) (hˡ Δ) ⟩
            s ∷ proj₁ (unzip Δ)
          ∎ where open ≡-Reasoning

        hᵃ : ∀ Δ → Null $ advertisements (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        hᵃ [] = refl
        hᵃ (_ ∷ []) = refl
        hᵃ (_ ∷ Δ@(_ ∷ _)) rewrite hᵃ Δ = L.++-identityʳ _

      namesʳ≡ : Γ′ ≡⟨on: namesʳ ⟩ Γ
      namesʳ≡ =
        begin
          namesʳ Γ′
        ≡⟨⟩
          namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ])
        ≡⟨ mapMaybe-++ isInj₂ (names (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)) (names (A auth[ ♯▷ ad ])) ⟩
          namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ namesʳ (A auth[ ♯▷ ad ])
        ≡⟨⟩
          namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ []
        ≡⟨ L.++-identityʳ _ ⟩
          namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
        ≡⟨ mapMaybe-++ isInj₂ (names Γ) (names (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)) ⟩
          namesʳ Γ ++ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        ≡⟨ cong (namesʳ Γ ++_) (hʳ Δ) ⟩
          namesʳ Γ ++ []
        ≡⟨ L.++-identityʳ _ ⟩
          namesʳ Γ
        ∎ where open ≡-Reasoning

      namesˡ≡ : namesˡ Γ′ ≡ namesˡ Γ ++ as
      namesˡ≡ =
        begin
          namesˡ Γ′
        ≡⟨ mapMaybe-++ isInj₁ (names $ Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (names $ A auth[ ♯▷ ad ]) ⟩
          namesˡ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ []
        ≡⟨ L.++-identityʳ _ ⟩
          namesˡ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
        ≡⟨ mapMaybe-++ isInj₁ (names Γ) (names $ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
          namesˡ Γ ++ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
        ≡⟨ cong (namesˡ Γ ++_) (hˡ Δ) ⟩
          namesˡ Γ ++ as
        ∎ where open ≡-Reasoning

      ads≡ : advertisements Γ′ ≡ advertisements Γ ++ advertisements (A auth[ ♯▷ ad ])
      ads≡ rewrite hᵃ Δ | L.++-identityʳ (advertisements Γ) = refl

      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ = liftʳ {Γ}{Γ′} namesʳ≡

      sechash↝ :  Γ ↝⟨ Sechash ⟩ Γ′
      sechash↝ sechash′ = extend-↦ (↭-reflexive namesˡ≡) sechash′ sechash⁺

      κ↝ : Γ ↝⟨ 𝕂² ⟩ Γ′
      κ↝ κ′ = extend-↦ (↭-reflexive ads≡) κ′ κ″
        where
          κ″ : advertisements (A auth[ ♯▷ ad ]) ↦′ 𝕂²′
          κ″ x∈ with does (A ∈? Hon) | x∈
          ... | true  | here refl = k⃗
          ... | false | ()

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ sechash↝ κ↝ public

  module _ ad Γ₀ A x where
    private
      g = G ad
      Γ = ` ad ∣ Γ₀
      Γ′ = Γ ∣ A auth[ x ▷ˢ ad ]
    module H₃ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      names≡ : Γ′ ≡⟨on: names ⟩ Γ
      names≡ = L.++-identityʳ _

      namesʳ≡ : Γ′ ≡⟨on: namesʳ ⟩ Γ
      namesʳ≡ = cong filter₂ names≡

      namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
      namesˡ≡ = cong filter₁ names≡

      ads≡ : Γ′ ≡⟨on: advertisements ⟩ Γ
      ads≡ = L.++-identityʳ _

      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ txout′ rewrite namesʳ≡ = txout′

      sechash↝ : Γ ↝⟨ Sechash ⟩ Γ′
      sechash↝ sechash′ rewrite namesˡ≡ = sechash′

      κ↝ : Γ ↝⟨ 𝕂² ⟩ Γ′
      κ↝ κ′ rewrite L.++-identityʳ (advertisements Γ) = κ′

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ sechash↝ κ↝ public

      module H₃′ (ad∈ : ad ∈ authorizedHonAds Γ₀) (names⊆ : g ⊆⟨on:names⟩ Γ₀) where

        txout↝′ : Γ ↝⟨ Txout ⟩ g
        txout↝′ txout′ = weaken-↦ txout′ (mapMaybe-⊆ isInj₂ names⊆)

        sechash↝′ : Γ ↝⟨ Sechash ⟩ g
        sechash↝′ sechash′ = weaken-↦ sechash′ (mapMaybe-⊆ isInj₁ names⊆)

        ad∈′ : ad ∈ advertisements R
        ad∈′ = ads⦅end⦆⊆ {R} $ ⟪ (λ ◆ → ad ∈ advertisements ◆) ⟫ cfg≡ ~: ad∈

        open Lift₀ 𝕣 t Γ cfg≡ ad txout↝′ sechash↝′ ad∈′ public

  module _ ad Γ₀ (ds : List DepositRef) partG v z where
    private
      g = G ad
      c = C ad

      -- [BUG] cannot get this to work here without explicitly passing ⦃ HPᵖ ⦄
      -- partG : List Participant
      -- partG = nub-participants g
      -- [WORKAROUND] give it as module parameters (forgetting the fact that it's computed out of `g`

      Γ₁ = ` ad ∣ Γ₀
      Γ₂ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) (ds)
      Γ₃ = || map (_auth[ ♯▷ ad ]) partG
      Γ  = Γ₁ ∣ Γ₂ ∣ Γ₃
      Γ′ = ⟨ c , v ⟩at z ∣ Γ₀

    module H₄ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      private
        h₀ : ∀ ps → Null $ namesʳ (|| map (_auth[ ♯▷ ad ]) ps)
        h₀ [] = refl
        h₀ (_ ∷ []) = refl
        h₀ (_ ∷ ps@(_ ∷ _)) = h₀ ps

        h₀′ : ∀ (ds : List DepositRef) →
          namesʳ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds) ≡ map (proj₂ ∘ proj₂) ds
        h₀′ [] = refl
        h₀′ (_ ∷ []) = refl
        h₀′ ((Aᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) =
          begin
            namesʳ ((⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ∣ Γ″)
          ≡⟨ mapMaybe-++ isInj₂ (names $ ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) (names Γ″) ⟩
            namesʳ (⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ++ namesʳ Γ″
          ≡⟨ cong (_++ namesʳ Γ″) (mapMaybe-++ isInj₂ (names $ ⟨ Aᵢ has vᵢ ⟩at xᵢ) (names $ Aᵢ auth[ xᵢ ▷ˢ ad ])) ⟩
            (xᵢ ∷ namesʳ (Aᵢ auth[ xᵢ ▷ˢ ad ])) ++ namesʳ Γ″
          ≡⟨ cong (λ x → (xᵢ ∷ x) ++ namesʳ Γ″) (L.++-identityʳ _) ⟩
            xᵢ ∷ namesʳ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds)
          ≡⟨ cong (xᵢ ∷_) (h₀′ ds) ⟩
            xᵢ ∷ map (proj₂ ∘ proj₂) ds
          ∎ where open ≡-Reasoning
                  Γ″ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds

        h₁ : ∀ (xs : List DepositRef) →
          Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) xs)
        h₁ [] = refl
        h₁ (_ ∷ []) = refl
        h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

        h₂ : ∀ xs → Null $ namesˡ (|| map (_auth[ ♯▷ ad ]) xs)
        h₂ [] = refl
        h₂ (_ ∷ []) = refl
        h₂ (_ ∷ xs@(_ ∷ _)) = h₂ xs

        h₁′ : ∀ (xs : List DepositRef) →
          Null $ advertisements (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) xs)
        h₁′ [] = refl
        h₁′ (_ ∷ []) = refl
        h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

      namesʳ≡₀ : namesʳ Γ ≡ namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
      namesʳ≡₀ =
        begin
          namesʳ Γ
        ≡⟨ mapMaybe-++ isInj₂ (names $ Γ₁ ∣ Γ₂) (names Γ₃) ⟩
          namesʳ (Γ₁ ∣ Γ₂) ++ namesʳ Γ₃
        ≡⟨ cong (namesʳ (Γ₁ ∣ Γ₂) ++_) (h₀ partG) ⟩
          namesʳ (Γ₁ ∣ Γ₂) ++ []
        ≡⟨ L.++-identityʳ _ ⟩
          namesʳ (Γ₁ ∣ Γ₂)
        ≡⟨ mapMaybe-++ isInj₂ (names $ Γ₁) (names Γ₂) ⟩
          namesʳ Γ₁ ++ namesʳ Γ₂
        ≡⟨ cong (_++ namesʳ Γ₂) (mapMaybe-++ isInj₂ (names $ ` ad) (names Γ₀)) ⟩
          namesʳ Γ₀ ++ namesʳ Γ₂
        ≡⟨ cong (namesʳ Γ₀ ++_) (h₀′ ds) ⟩
          namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
        ∎ where open ≡-Reasoning

      namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
      namesˡ≡ = sym $
        begin namesˡ Γ                      ≡⟨⟩
              namesˡ (Γ₁ ∣ Γ₂ ∣ Γ₃)         ≡⟨ mapMaybe-++ isInj₁ (names $ Γ₁ ∣ Γ₂) (names Γ₃) ⟩
              namesˡ (Γ₁ ∣ Γ₂) ++ namesˡ Γ₃ ≡⟨ cong (namesˡ (Γ₁ ∣ Γ₂)  ++_) (h₂ partG) ⟩
              namesˡ (Γ₁ ∣ Γ₂) ++ []        ≡⟨ L.++-identityʳ _ ⟩
              namesˡ (Γ₁ ∣ Γ₂)              ≡⟨ mapMaybe-++ isInj₁ (names Γ₁) (names Γ₂) ⟩
              namesˡ Γ₁ ++ namesˡ Γ₂        ≡⟨ cong (namesˡ Γ₁ ++_) (h₁ ds) ⟩
              namesˡ Γ₁ ++ []               ≡⟨ L.++-identityʳ _ ⟩
              namesˡ Γ₁                     ≡⟨⟩
              namesˡ Γ′                     ∎ where open ≡-Reasoning

      ads⊆ : Γ′ ⊆⟨on: advertisements ⟩ Γ
      ads⊆ = ∈-++⁺ˡ ∘ ∈-++⁺ˡ
        {- T0D0: update to stdlib#v1.5 to fix `infixr step-⊆`
        begin
          advertisements Γ′
        ≡⟨⟩
          advertisements Γ₀
        ⊆⟨ {!!} ⟩
          advertisements Γ
        ∎
        where open ⊆-Reasoning Advertisement
        -}

      module H₄′ (honG : Any (_∈ Hon) partG) (names⊆ : g ⊆⟨on:names⟩ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ˡ ∘ ∈-++⁺ˡ ∘ ∈-++⁺ʳ (names $ ` ad)

        txout↝ : Γ ↝⟨ Txout ⟩ g
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ ↝⟨ Sechash ⟩ g
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        authH : ∀ {cs : List Configuration}
          → Any (λ c → ad ∈ advertisements c) cs
          → ad ∈ advertisements (|| cs)
        authH {cs = c ∷ []} p with p
        ... | here ad∈ = ad∈
        authH {cs = _ ∷ _ ∷ cs} p with p
        ... | here  ad∈ = ∈-++⁺ˡ ad∈
        ... | there ad∈ = ∈-++⁺ʳ _ (authH ad∈)

        ad∈₀ : ad ∈ advertisements Γ₃
        ad∈₀ = authH h′
          where
            h : ∀ {p} → p ∈ Hon → ad ∈ advertisements (p auth[ ♯▷ ad ])
            h {p} p∈ rewrite dec-true (p ∈? Hon) p∈ = here refl

            h′ : Any (λ ◆ → ad ∈ advertisements ◆) (map (_auth[ ♯▷ ad ]) partG)
            h′ = L.Any.map⁺ {f = _auth[ ♯▷ ad ]} (L.Any.map h honG)

        ad∈ : ad ∈ advertisements Γ
        ad∈ = ∈-++⁺ʳ (advertisements $ Γ₁ ∣ Γ₂) ad∈₀

        ad∈′ : ad ∈ advertisements R
        ad∈′ = ads⦅end⦆⊆ {R} $ ⟪ (λ ◆ → ad ∈ advertisements ◆) ⟫ cfg≡ ~: ad∈

        open Lift₀ 𝕣 t Γ cfg≡ ad txout↝ sechash↝ ad∈′ public

      module H₄″ (tx : TxInput′) where

        sechash↝′ :  Γ ↝⟨ Sechash ⟩ Γ′
        sechash↝′ = liftˡ {Γ}{Γ′} namesˡ≡

        κ↝′ : Γ ↝⟨ 𝕂² ⟩ Γ′
        κ↝′ κ′ = weaken-↦ κ′ ads⊆

        txout↝′ : Γ ↝⟨ Txout ⟩ Γ′
        txout↝′ txout′ rewrite namesʳ≡₀ = cons-↦ z tx $ weaken-↦ txout′ ∈-++⁺ˡ

        open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝′ sechash↝′ κ↝′ public

  module _ c v x Γ₀ A i where
    private
      Γ  = ⟨ c , v ⟩at x ∣ Γ₀
      Γ′ = ⟨ c , v ⟩at x ∣ A auth[ x ▷ (c ‼ i) ] ∣ Γ₀

    module H₅ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public

      module H₅′ ad (ad∈ : ad ∈ authorizedHonAdsʳ R) (names⊆ : G ad ⊆⟨on:names⟩ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ ↝⟨ Txout ⟩ G ad
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ ↝⟨ Sechash ⟩ G ad
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≡ ad txout↝ sechash↝ ad∈ public

  module _ c v y (ds : List (Participant × Value × Id)) Γ₀  c′ y′ where
    private
      vs = proj₁ $ proj₂ $ unzip₃ ds
      xs = proj₂ $ proj₂ $ unzip₃ ds
      Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₀)
      Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀
    module H₆ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      private
        h₁ : ∀ (ds : List (Participant × Value × Id)) →
          Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
        h₁ [] = refl
        h₁ (_ ∷ []) = refl
        h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

        h₁′ : ∀ (ds : List (Participant × Value × Id)) →
          Null $ advertisements (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
        h₁′ [] = refl
        h₁′ (_ ∷ []) = refl
        h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

      namesʳ≡₀ : namesʳ Γ ≡ (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
      namesʳ≡₀ =
        begin
          namesʳ Γ
        ≡⟨ mapMaybe-++ isInj₂ (inj₂ y ∷ names Γ₁) (names Γ₀) ⟩
          (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
        ∎ where open ≡-Reasoning

      namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
      namesˡ≡ =
        begin
          namesˡ Γ′
        ≡⟨ mapMaybe-++ isInj₁ (names $ ⟨ c′ , v + sum vs ⟩at y′) (names Γ₀) ⟩
          namesˡ (⟨ c′ , v + sum vs ⟩at y′) ++ namesˡ Γ₀
        ≡⟨⟩
          namesˡ Γ₀
        ≡˘⟨ L.++-identityˡ _ ⟩
          [] ++ namesˡ Γ₀
        ≡˘⟨ cong (_++ namesˡ Γ₀) (h₁ ds) ⟩
          namesˡ (⟨ c′ , v ⟩at y ∣ Γ₁) ++ namesˡ Γ₀
        ≡˘⟨ mapMaybe-++ isInj₁ (names $ ⟨ c′ , v ⟩at y ∣ Γ₁) (names Γ₀) ⟩
          namesˡ Γ
        ∎ where open ≡-Reasoning

      ads≡ : Γ′ ≡⟨on: advertisements ⟩ Γ
      ads≡ =
        begin
          advertisements Γ′
        ≡⟨⟩
          advertisements Γ₀
        ≡˘⟨ cong (_++ advertisements Γ₀) (h₁′ ds) ⟩
          advertisements Γ₁ ++ advertisements Γ₀
        ≡⟨⟩
          advertisements Γ
        ∎ where open ≡-Reasoning

      module H₆′ (tx : TxInput′) where

        sechash↝ :  Γ ↝⟨ Sechash ⟩ Γ′
        sechash↝ = liftˡ {Γ}{Γ′} namesˡ≡

        κ↝ : Γ ↝⟨ 𝕂² ⟩ Γ′
        κ↝ = liftᵃ {Γ}{Γ′} ads≡

        txout↝ : Γ ↝⟨ Txout ⟩ Γ′
        txout↝ txout′ rewrite namesʳ≡₀ = cons-↦ y′ tx $ weaken-↦ txout′ (∈-++⁺ʳ _)

        open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ sechash↝ κ↝ public

      module H₆″ ad (ad∈ : ad ∈ authorizedHonAdsʳ R) (names⊆ : G ad ⊆⟨on:names⟩ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ ↝⟨ Txout ⟩ G ad
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ ↝⟨ Sechash ⟩ G ad
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≡ ad txout↝ sechash↝ ad∈ public

  module _ A a n Γ₀ where
    private
      Γ  = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀
      Γ′ = A ∶ a ♯ n ∣ Γ₀
    module H₇ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public

  module _ c v y Γ₀  (vcis : List (Value × Contracts × Id)) where
    private
      Γ  = ⟨ c , v ⟩at y ∣ Γ₀
      xs = proj₂ $ proj₂ $ unzip₃ vcis
      Γ₁ = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis
      Γ′ = Γ₁ ∣ Γ₀
    module H₈ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      private
        hʳ : ∀ (vcis : List (Value × Contracts × Id)) →
          namesʳ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis) ≡ (proj₂ $ proj₂ $ unzip₃ vcis)
        hʳ [] = refl
        hʳ (_ ∷ []) = refl
        hʳ (_ ∷ xs@(_ ∷ _)) = cong (_ ∷_) (hʳ xs)

        hˡ : ∀ (vcis : List (Value × Contracts × Id)) →
          Null $ namesˡ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
        hˡ [] = refl
        hˡ (_ ∷ []) = refl
        hˡ (_ ∷ xs@(_ ∷ _)) = hˡ xs

        hᵃ : ∀ (vcis : List (Value × Contracts × Id)) →
          Null $ advertisements (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
        hᵃ [] = refl
        hᵃ (_ ∷ []) = refl
        hᵃ (_ ∷ xs@(_ ∷ _)) = hᵃ xs

      namesʳ≡₀ : namesʳ Γ ≡ y ∷ namesʳ Γ₀
      namesʳ≡₀ = mapMaybe-++ isInj₂ [ inj₂ y ] (names Γ₀)

      namesʳ≡ : namesʳ Γ′ ≡ xs ++ namesʳ Γ₀
      namesʳ≡ =
        begin
          namesʳ Γ′
        ≡⟨ mapMaybe-++ isInj₂ (names Γ₁) (names Γ₀) ⟩
          namesʳ Γ₁ ++ namesʳ Γ₀
        ≡⟨ cong (_++ namesʳ Γ₀) (hʳ vcis) ⟩
          xs ++ namesʳ Γ₀
        ∎ where open ≡-Reasoning

      namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
      namesˡ≡ =
        begin
          namesˡ Γ′
        ≡⟨ mapMaybe-++ isInj₁ (names Γ₁) (names Γ₀) ⟩
          namesˡ Γ₁ ++ namesˡ Γ₀
        ≡⟨ cong (_++ namesˡ Γ₀) (hˡ vcis) ⟩
          namesˡ Γ₀
        ≡⟨⟩
          namesˡ Γ
        ∎ where open ≡-Reasoning

      ads≡ : Γ′ ≡⟨on: advertisements ⟩ Γ
      ads≡ =
        begin
          advertisements Γ′
        ≡⟨ cong (_++ advertisements Γ₀) (hᵃ vcis) ⟩
          advertisements Γ₀
        ≡⟨⟩
          advertisements Γ
        ∎ where open ≡-Reasoning

      module H₈′ (txout⁺ : xs ↦ TxInput′) where

        txout↝ : Γ ↝⟨ Txout ⟩ Γ′
        txout↝ txout′ rewrite namesʳ≡₀ = extend-↦ (↭-reflexive namesʳ≡) txout⁺ (weaken-↦ txout′ there)

        sechash↝ : Γ ↝⟨ Sechash ⟩ Γ′
        sechash↝ = liftˡ {Γ}{Γ′} namesˡ≡

        κ↝ : Γ ↝⟨ 𝕂² ⟩ Γ′
        κ↝ = liftᵃ {Γ}{Γ′} ads≡

        open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ sechash↝ κ↝ public

      module H₈″ ad (ad∈ : ad ∈ authorizedHonAdsʳ R) (names⊆ : G ad ⊆⟨on:names⟩ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ ↝⟨ Txout ⟩ G ad
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ ↝⟨ Sechash ⟩ G ad
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≡ ad txout↝ sechash↝ ad∈ public

  module _ c v y Γ₀ A x where
    private
      Γ  = ⟨ c , v ⟩at y ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ Γ₀
    module H₉ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where

      module H₉′ (tx : TxInput′) where
        txout↝ : Γ ↝⟨ Txout ⟩ Γ′
        txout↝  txout′ = cons-↦ x tx $ weaken-↦ txout′ there

        open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ id id public

      module H₉″ ad (ad∈ : ad ∈ authorizedHonAdsʳ R) (names⊆ : G ad ⊆⟨on:names⟩ Γ₀) where

        n⊆ : names Γ₀ ⊆ names Γ
        n⊆ = ∈-++⁺ʳ _

        txout↝ : Γ ↝⟨ Txout ⟩ G ad
        txout↝ txout′ = weaken-↦ txout′ $ mapMaybe-⊆ isInj₂ (n⊆ ∘ names⊆)

        sechash↝ : Γ ↝⟨ Sechash ⟩ G ad
        sechash↝ sechash′ = weaken-↦ sechash′ $ mapMaybe-⊆ isInj₁ (n⊆ ∘ names⊆)

        open Lift₀ 𝕣 t Γ cfg≡ ad txout↝ sechash↝ ad∈ public


  module _ A v x v′ x′ Γ₀ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
    module H₁₀ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public

  module _ A v x v′ x′ y Γ₀ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
      Γ′ = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
    module H₁₁ (cfg≡ : R ≡⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ (λ x∈ → there (there x∈))

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ id id public

  module _ A v v′ x Γ₀ where
    private
      Γ  = ⟨ A has (v + v′) ⟩at x ∣ Γ₀
      Γ′ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
    module H₁₂ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public

  module _ A v v′ x Γ₀ y y′ where
    private
      Γ  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
    module H₁₃ (cfg≡ : R ≡⋯ Γ at t) (tx tx′ : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ txout′ = cons-↦ y tx $ cons-↦ y′ tx′ $ weaken-↦ txout′ there

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ id id public

  module _ A v x Γ₀ B′ where
    private
      Γ  = ⟨ A has v ⟩at x ∣ Γ₀
      Γ′ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
    module H₁₄ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public

  module _ A v x B′ Γ₀ y where
    private
      Γ  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
      Γ′ = ⟨ B′ has v ⟩at y ∣ Γ₀
    module H₁₅ (cfg≡ : R ≡⋯ Γ at t) (tx : TxInput′) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ txout′ = cons-↦ y tx $ weaken-↦ txout′ there

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ id id public

  module _ (ds : List (Participant × Value × Id)) Γ₀ (j : Index ds) A y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
      Γ  = Δ ∣ Γ₀
      j′ = Index xs ∋ ‼-map {xs = ds} j
      Γ′ = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀

    module H₁₆ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where

      -- ** name resolution
      xs⊆ : xs ⊆ namesʳ R
      xs⊆ = subst (λ ◆ → xs ⊆ namesʳ ◆) (sym cfg≡)
          $ ⊆-trans (namesʳ-∥map-helper ds) (mapMaybe-⊆ isInj₂ $ ∈-++⁺ˡ {xs = names Δ} {ys = names Γ₀})

      xs↦ : xs ↦ TxInput′
      xs↦ = txout′ ∘ xs⊆
      --

      names≡ : Γ′ ≡⟨on: names ⟩ Γ
      names≡ rewrite L.++-identityʳ (names Δ) = refl

      namesʳ≡ :  Γ′ ≡⟨on: namesʳ ⟩ Γ
      namesʳ≡ = cong filter₂ names≡

      namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
      namesˡ≡ = cong filter₁ names≡

      ads≡ : Γ′ ≡⟨on: advertisements ⟩ Γ
      ads≡ rewrite L.++-identityʳ (advertisements Δ) = refl

      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ = liftʳ {Γ}{Γ′} namesʳ≡

      sechash↝ : Γ ↝⟨ Sechash ⟩ Γ′
      sechash↝  = liftˡ {Γ}{Γ′} namesˡ≡

      κ↝ : Γ ↝⟨ 𝕂² ⟩ Γ′
      κ↝ = liftᵃ {Γ}{Γ′} ads≡

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ sechash↝ κ↝ public

  module _ (ds : List (Participant × Value × Id)) Γ₀ y where
    private
      xs = map (proj₂ ∘ proj₂) ds
      Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds)
      Γ  = Δ ∣ Γ₀
      Γ′ = Γ₀
    module H₁₇ (cfg≡ : R ≡⋯ Γ at t) (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where

      -- ** name resolution
      xs⊆ : xs ⊆ namesʳ R
      xs⊆ = subst (λ ◆ → xs ⊆ namesʳ ◆) (sym cfg≡)
          $ ⊆-trans (namesʳ-∥map-helper′ ds) (mapMaybe-⊆ isInj₂ $ ∈-++⁺ˡ {xs = names Δ} {ys = names Γ₀})

      xs↦ : xs ↦ TxInput′
      xs↦ = txout′ ∘ xs⊆
      --

      namesˡ≡₀ : namesˡ Γ ≡ namesˡ Δ ++ namesˡ Γ₀
      namesˡ≡₀ = mapMaybe-++ isInj₁ (names Δ) (names Γ₀)

      namesʳ≡₀ : namesʳ Γ ≡ namesʳ Δ ++ namesʳ Γ₀
      namesʳ≡₀ = mapMaybe-++ isInj₂ (names Δ) (names Γ₀)

      txout↝ : Γ ↝⟨ Txout ⟩ Γ′
      txout↝ txout′ rewrite namesʳ≡₀ = weaken-↦ txout′ (∈-++⁺ʳ _)

      sechash↝ : Γ ↝⟨ Sechash ⟩ Γ′
      sechash↝ sechash′ rewrite namesˡ≡₀ = weaken-↦ sechash′ (∈-++⁺ʳ _)

      κ↝ : Γ ↝⟨ 𝕂² ⟩ Γ′
      κ↝ κ′ = weaken-↦ κ′ (∈-++⁺ʳ _)

      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ txout↝ sechash↝ κ↝ public

  module _ Γ (cfg≡ : R ≡⋯ Γ at t) where
    private
      Γ′ = Γ
    module H₁₈ (Γ→Γ′ : Γ at t —[ α ]→ₜ Γ′ at t′) where
      open Lift 𝕣 t α t′ Γ cfg≡ Γ′ Γ→Γ′ id id id public
