{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Accessors
open import Prelude.Decidable
open import Prelude.Lists.Collections
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Membership
open import Prelude.Lists.Concat
open import Prelude.Lists.MapMaybe
open import Prelude.InferenceRules
open import Prelude.Coercions

open import Bitcoin.Tx.Base using (_∙Value; _∙value)
open import BitML.BasicTypes using (⋯)

module SymbolicModel.Run.Accessors (⋯ : ⋯) where

open import SymbolicModel.Run.Base ⋯
  hiding (begin_; _∎)
open import SymbolicModel.Run.Collections ⋯
open ≡-Reasoning

infix 100 _∙cfg
unquoteDecl _∙Cfg _∙cfg ∙cfg=_ = genAccessor _∙Cfg _∙cfg ∙cfg=_ (quote Cfg)
instance
  Cfgᵗ∙Cfg : Cfgᵗ ∙Cfg
  Cfgᵗ∙Cfg = ∙cfg= cfg

  Run∙Cfg : Run ∙Cfg
  Run∙Cfg = ∙cfg= (cfg ∘ end)

instance
  Ids∙Value : (∃ λ (Γ : Cfg) → (x ∈ ids Γ)) ∙Value
  Ids∙Value ._∙ = uncurry go
    where
      go : ∀ (Γ : Cfg) → x ∈ ids Γ → Value
      go (⟨ _ , v ⟩at _)   (here refl) = v
      go (⟨ _ has v ⟩at _) (here refl) = v
      go (l ∣ r) x∈ with ∈-ids-++⁻ l r x∈
      ... | inj₁ x∈ˡ = go l x∈ˡ
      ... | inj₂ x∈ʳ = go r x∈ʳ

  Idsʳ∙Value : (∃ λ (R : Run) → (x ∈ ids R)) ∙Value
  Idsʳ∙Value {x} ._∙ (R , x∈) = {!!}
{-
    let y , y∈ , eq = ∈-mapMaybe⁻ isInj₂ {xs = names R} x∈ in
    let z∈ = ∈-concatMap⁻ collect {y}{allCfgs R} y∈ in
    let z∈ = ∈-mapMaybe⁺ isInj₂ z∈ in
    let z , p = L.Any.satisfied z∈ in

    (z , {!∈-mapMaybe⁺ isInj₂ p!}) ∙value

    -- ( ∃ (λ Γ → x ∈ ids Γ)
    -- ∋ L.Any.satisfied
    --     ( Any (λ Γ → x ∈ ids Γ) (allCfgs R)
    --     ∋ ∈-concatMap⁻ {A = Cfg} ids
    --       (∈-concatMap⁺ ids {!(L.Any.satisfied $ ∈-mapMaybe⁺ isInj₂ z∈) ∙value!})
    --         -- ∈-concatMap⁻ {A = Cfg} ids
    --          -- {!∈-mapMaybe⁺ isInj₂ {xs = names R} y∈ eq!}
    --         --
    --         --  (∈-mapMaybe⁺ isInj₂ {y} y∈ eq)
    --     )
    -- )
    -- ∙value
-}

∈-ids-++⁻⇒∈-ids-++⁺ : ∀ (x∈ : x ∈ ids (Γ ∣ Γ′)) →
  case ∈-ids-++⁻ Γ Γ′ x∈ of λ where
    (inj₁ x∈ˡ) → x∈ ≡ ∈-ids-++⁺ˡ Γ Γ′ x∈ˡ
    (inj₂ x∈ʳ) → x∈ ≡ ∈-ids-++⁺ʳ Γ Γ′ x∈ʳ
∈-ids-++⁻⇒∈-ids-++⁺ {x}{Γ}{Γ′} x∈ = {!!}

∈-ids-resp-≈ : ∀ l c r →
  (l ∣ (c ∣ r)) ⊆⦅ ids ⦆ (l ∣ c ∣ r)
∈-ids-resp-≈ l c r =
  ∈namesʳ-resp-≈ _ {l ∣ (c ∣ r)}{l ∣ c ∣ r} (≈ᶜ-assoc l c r)

∈-ids-++⁺ˡ∘∈-ids-++⁺ˡ : ∀ l c r (x∈ : x ∈ ids l)
  → ( ∈-ids-++⁺ˡ (l ∣ c) r
    ∘ ∈-ids-++⁺ˡ l c
    ) x∈
  ≡ ( ∈-ids-resp-≈ l c r
    ∘ ∈-ids-++⁺ˡ l (c ∣ r)
    ) x∈
∈-ids-++⁺ˡ∘∈-ids-++⁺ˡ l c r x∈ = {!!}

∈-ids-++⁺ˡ∘∈-ids-++⁺ʳ : ∀ l c r (x∈ : x ∈ ids c)
  → ( ∈-ids-++⁺ˡ (l ∣ c) r
    ∘ ∈-ids-++⁺ʳ l c
    ) x∈
  ≡ ( ∈-ids-resp-≈ l c r
    ∘ ∈-ids-++⁺ʳ l (c ∣ r)
    ∘ ∈-ids-++⁺ˡ c r
    ) x∈
∈-ids-++⁺ˡ∘∈-ids-++⁺ʳ l c r x∈ = {!!}

∈-ids-assoc-⊎ : ∀ l c r
  → (x ∈ ids l) ⊎ (x ∈ ids (c ∣ r))
  → (x ∈ ids (l ∣ c)) ⊎ (x ∈ ids r)
∈-ids-assoc-⊎ l c r = λ where
  (inj₁ x∈) → inj₁ (∈-ids-++⁺ˡ l c x∈)
  (inj₂ x∈) → case ∈-ids-++⁻ c r x∈ of λ where
    (inj₁ x∈) → inj₁ (∈-ids-++⁺ʳ l c x∈)
    (inj₂ x∈) → inj₂ x∈

∈-ids-assoc-⊎∘inj₂∘∈-ids-++⁺ˡ : ∀ l c r (x∈ : x ∈ ids c)
  → ( ∈-ids-assoc-⊎ l c r
    ∘ inj₂
    ∘ ∈-ids-++⁺ˡ c r
    ) x∈
  ≡ inj₁ (∈-ids-++⁺ʳ l c x∈)
∈-ids-assoc-⊎∘inj₂∘∈-ids-++⁺ˡ l c r x∈ = {!!}

∈-ids-++⁻∘∈-ids-resp-≈ : ∀ l c r (x∈ : x ∈ ids (l ∣ (c ∣ r)))
  → ( ∈-ids-++⁻ (l ∣ c) r
    ∘ ∈-ids-resp-≈ l c r
    ) x∈
  ≡ ( ∈-ids-assoc-⊎ l c r
    ∘ ∈-ids-++⁻ l (c ∣ r)
    ) x∈
∈-ids-++⁻∘∈-ids-resp-≈ l c r x∈ = {!!}

mutual
  ∈-ids-++⁻∘∈-ids-++⁺ˡ : ∀ (x∈ : x ∈ ids Γ)
    → ∈-ids-++⁻ Γ Γ′ (∈-ids-++⁺ˡ Γ Γ′ x∈)
    ≡ inj₁ x∈
  ∈-ids-++⁻∘∈-ids-++⁺ˡ {Γ = ⟨ _ , _ ⟩at _}   (here refl) = refl
  ∈-ids-++⁻∘∈-ids-++⁺ˡ {Γ = ⟨ _ has _ ⟩at _} (here refl) = refl
  ∈-ids-++⁻∘∈-ids-++⁺ˡ {Γ = l ∣ r}{Γ′} x∈
    with ∈-ids-++⁻ l r x∈ | ∈-ids-++⁻⇒∈-ids-++⁺ {Γ = l}{r} x∈
  ... | inj₁ x∈ˡ | refl
    = begin
      ( ∈-ids-++⁻ (l ∣ r) Γ′
      ∘ ∈-ids-++⁺ˡ (l ∣ r) Γ′
      ∘ ∈-ids-++⁺ˡ l r
      ) x∈ˡ
    ≡⟨ cong (∈-ids-++⁻ (l ∣ r) Γ′) $ ∈-ids-++⁺ˡ∘∈-ids-++⁺ˡ l r Γ′ _ ⟩
      ( ∈-ids-++⁻ (l ∣ r) Γ′
      ∘ ∈-ids-resp-≈ l r Γ′
      ∘ ∈-ids-++⁺ˡ l (r ∣ Γ′)
      ) x∈ˡ
    ≡⟨ ∈-ids-++⁻∘∈-ids-resp-≈ l r Γ′ _ ⟩
      ( ∈-ids-assoc-⊎ l r Γ′
      ∘ ∈-ids-++⁻ l (r ∣ Γ′)
      ∘ ∈-ids-++⁺ˡ l (r ∣ Γ′)
      ) x∈ˡ
    ≡⟨ cong (∈-ids-assoc-⊎ l r Γ′) $ ∈-ids-++⁻∘∈-ids-++⁺ˡ {Γ = l}{r ∣ Γ′} x∈ˡ ⟩
      ∈-ids-assoc-⊎ l r Γ′ (inj₁ x∈ˡ)
    ≡⟨⟩
      inj₁ (∈-ids-++⁺ˡ l r x∈ˡ)
    ∎
  ... | inj₂ x∈ʳ | refl
    = begin
      ( ∈-ids-++⁻ (l ∣ r) Γ′
      ∘ ∈-ids-++⁺ˡ (l ∣ r) Γ′
      ∘ ∈-ids-++⁺ʳ l r
      ) x∈ʳ
    ≡⟨ cong (∈-ids-++⁻ (l ∣ r) Γ′) $ ∈-ids-++⁺ˡ∘∈-ids-++⁺ʳ l r Γ′ _ ⟩
      ( ∈-ids-++⁻ (l ∣ r) Γ′
      ∘ ∈-ids-resp-≈ l r Γ′
      ∘ ∈-ids-++⁺ʳ l (r ∣ Γ′)
      ∘ ∈-ids-++⁺ˡ r Γ′
      ) x∈ʳ
    ≡⟨ ∈-ids-++⁻∘∈-ids-resp-≈ l r Γ′ _ ⟩
      ( ∈-ids-assoc-⊎ l r Γ′
      ∘ ∈-ids-++⁻ l (r ∣ Γ′)
      ∘ ∈-ids-++⁺ʳ l (r ∣ Γ′)
      ∘ ∈-ids-++⁺ˡ r Γ′
      ) x∈ʳ
    ≡⟨ cong (∈-ids-assoc-⊎ l r Γ′) $ ∈-ids-++⁻∘∈-ids-++⁺ʳ {Γ′ = r ∣ Γ′}{l} _ ⟩
      ( ∈-ids-assoc-⊎ l r Γ′
      ∘ inj₂
      ∘ ∈-ids-++⁺ˡ r Γ′
      ) x∈ʳ
    ≡⟨ ∈-ids-assoc-⊎∘inj₂∘∈-ids-++⁺ˡ l r Γ′ _ ⟩
      inj₁ (∈-ids-++⁺ʳ l r x∈ʳ)
    ∎

  postulate
    ∈-ids-++⁻∘∈-ids-++⁺ʳ : ∀ (x∈ : x ∈ ids Γ′)
      → ∈-ids-++⁻ Γ Γ′ (∈-ids-++⁺ʳ Γ Γ′ x∈)
      ≡ inj₂ x∈
{-
  ∈-ids-++⁻∘∈-ids-++⁺ʳ {Γ′ = ⟨ _ , _ ⟩at _}   (here refl) = {!!}
  ∈-ids-++⁻∘∈-ids-++⁺ʳ {Γ′ = ⟨ _ has _ ⟩at _} (here refl) = {!!}
  ∈-ids-++⁻∘∈-ids-++⁺ʳ {Γ′ = l ∣ r}{Γ} x∈
    with ∈-ids-++⁻ l r x∈ | ∈-ids-++⁻⇒∈-ids-++⁺ {Γ = l}{r} x∈
  ... | inj₁ x∈ˡ | refl
    = begin
      ( ∈-ids-++⁻ Γ (l ∣ r)
      ∘ ∈-ids-++⁺ʳ Γ (l ∣ r)
      ∘ ∈-ids-++⁺ˡ l r
      ) x∈ˡ
    ≡⟨ {!!} ⟩
      inj₂ (∈-ids-++⁺ˡ l r x∈ˡ)
    ∎
  ... | inj₂ x∈ʳ | refl
    = begin
      ( ∈-ids-++⁻ Γ (l ∣ r)
      ∘ ∈-ids-++⁺ʳ Γ (l ∣ r)
      ∘ ∈-ids-++⁺ʳ l r
      ) x∈ʳ
    ≡⟨ {!!} ⟩
      inj₂ (∈-ids-++⁺ʳ l r x∈ʳ)
    ∎
-}

∈-ids-++⁺ˡ∙value : ∀ (x∈ : x ∈ ids Γ)
 → (Γ ∣ Γ′ , ∈-ids-++⁺ˡ Γ Γ′ x∈) ∙value
 ≡ (Γ , x∈) ∙value
∈-ids-++⁺ˡ∙value {x}{Γ}{Γ′} x∈
  with ∈-ids-++⁻ Γ Γ′ (∈-ids-++⁺ˡ Γ Γ′ x∈) | ∈-ids-++⁻∘∈-ids-++⁺ˡ {x}{Γ}{Γ′} x∈
... | .(inj₁ x∈) | refl = refl

∈-ids-++⁺ʳ∙value : ∀ (x∈ : x ∈ ids Γ′)
 → (Γ ∣ Γ′ , ∈-ids-++⁺ʳ Γ Γ′ x∈) ∙value
 ≡ (Γ′ , x∈) ∙value
∈-ids-++⁺ʳ∙value {x}{Γ′}{Γ} x∈
  with ∈-ids-++⁻ Γ Γ′ (∈-ids-++⁺ʳ Γ Γ′ x∈) | ∈-ids-++⁻∘∈-ids-++⁺ʳ {x}{Γ′}{Γ} x∈
... | .(inj₂ x∈) | refl = refl

c∈⇒x∈∙value : ∀ (c∈ : ⟨ c , v ⟩at x ∈ᶜ Γ) →
  (Γ , c∈⇒x∈ Γ c∈) ∙value ≡ v
c∈⇒x∈∙value {Γ = ` _} c∈ = contradict c∈
c∈⇒x∈∙value {Γ = ⟨ _ has _ ⟩at _} c∈ = contradict c∈
c∈⇒x∈∙value {Γ = _ auth[ _ ]} c∈ = contradict c∈
c∈⇒x∈∙value {Γ = ⟨ _ ∶ _ ♯ _ ⟩} c∈ = contradict c∈
c∈⇒x∈∙value {Γ = _ ∶ _ ♯ _} c∈ = contradict c∈
c∈⇒x∈∙value {Γ = ⟨ c , v ⟩at x} (here refl) = refl
c∈⇒x∈∙value {Γ = l ∣ r} c∈
  with destruct-∈ᶜ-++ l r c∈
... | inj₁ (c∈ˡ , refl)
  rewrite c∈⇒x∈∘∈ᶜ-++⁺ˡ {Γ  = l}{r} c∈ˡ
        | ∈-ids-++⁻∘∈-ids-++⁺ˡ {Γ = l}{r} (c∈⇒x∈ l c∈ˡ)
        = c∈⇒x∈∙value {Γ = l} c∈ˡ
... | inj₂ (c∈ʳ , refl)
  rewrite c∈⇒x∈∘∈ᶜ-++⁺ʳ {Γ′ = r}{l} c∈ʳ
        | ∈-ids-++⁻∘∈-ids-++⁺ʳ {Γ′ = r}{l} (c∈⇒x∈ r c∈ʳ)
        = c∈⇒x∈∙value {Γ = r} c∈ʳ

≈-base :
  ∙ IsBase Γ
  ∙ Γ′ ≈ Γ
    ─────────
    Γ′ ≡ Γ
≈-base {` _} {∅ᶜ} _ Γ≈
  = ⊥-elim $ L.Perm.¬x∷xs↭[] (↭-sym Γ≈)
≈-base {⟨ _ , _ ⟩at _} {∅ᶜ} _ Γ≈
  = ⊥-elim $ L.Perm.¬x∷xs↭[] (↭-sym Γ≈)
≈-base {⟨ _ has _ ⟩at _} {∅ᶜ} _ Γ≈
  = ⊥-elim $ L.Perm.¬x∷xs↭[] (↭-sym Γ≈)
≈-base {_ auth[ _ ]} {∅ᶜ} _ Γ≈
  = ⊥-elim $ L.Perm.¬x∷xs↭[] (↭-sym Γ≈)
≈-base {⟨ _ ∶ _ ♯ _ ⟩} {∅ᶜ} _ Γ≈
  = ⊥-elim $ L.Perm.¬x∷xs↭[] (↭-sym Γ≈)
≈-base {_ ∶ _ ♯ _} {∅ᶜ} _ Γ≈
  = ⊥-elim $ L.Perm.¬x∷xs↭[] (↭-sym Γ≈)
≈-base {` _} {` _} _ Γ≈
  = cong to[ Cfg ] $ sym $ []-injective $ L.Perm.↭-singleton-inv (↭-sym Γ≈)
≈-base {⟨ _ , _ ⟩at _} {` _} _ Γ≈
  = case []-injective $ L.Perm.↭-singleton-inv (↭-sym Γ≈) of λ ()
≈-base {⟨ A has v ⟩at x} {` ad} b Γ≈ = {!!}
≈-base {A auth[ a ]} {` ad} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {` ad} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {` ad} b Γ≈ = {!!}
≈-base {` ad} {⟨ c , v ⟩at x} b Γ≈ = {!!}
≈-base {⟨ c , v ⟩at x} {⟨ c₁ , v₁ ⟩at x₁} b Γ≈ = {!!}
≈-base {⟨ A has v ⟩at x} {⟨ c , v₁ ⟩at x₁} b Γ≈ = {!!}
≈-base {A auth[ a ]} {⟨ c , v ⟩at x} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {⟨ c , v ⟩at x} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {⟨ c , v ⟩at x} b Γ≈ = {!!}
≈-base {` ad} {⟨ A has v ⟩at x} b Γ≈ = {!!}
≈-base {⟨ c , v ⟩at x} {⟨ A has v₁ ⟩at x₁} b Γ≈ = {!!}
≈-base {⟨ A has v ⟩at x} {⟨ A₁ has v₁ ⟩at x₁} b Γ≈ = {!!}
≈-base {A auth[ a ]} {⟨ A₁ has v ⟩at x} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {⟨ A₁ has v ⟩at x} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {⟨ A₁ has v ⟩at x} b Γ≈ = {!!}
≈-base {` ad} {A auth[ a ]} b Γ≈ = {!!}
≈-base {⟨ c , v ⟩at x} {A auth[ a ]} b Γ≈ = {!!}
≈-base {⟨ A has v ⟩at x} {A₁ auth[ a ]} b Γ≈ = {!!}
≈-base {A auth[ a ]} {A₁ auth[ a₁ ]} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {A₁ auth[ a ]} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {A₁ auth[ a ]} b Γ≈ = {!!}
≈-base {` ad} {⟨ A ∶ s ♯ mn ⟩} b Γ≈ = {!!}
≈-base {⟨ c , v ⟩at x} {⟨ A ∶ s ♯ mn ⟩} b Γ≈ = {!!}
≈-base {⟨ A has v ⟩at x} {⟨ A₁ ∶ s ♯ mn ⟩} b Γ≈ = {!!}
≈-base {A auth[ a ]} {⟨ A₁ ∶ s ♯ mn ⟩} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {⟨ A₁ ∶ s₁ ♯ mn₁ ⟩} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {⟨ A₁ ∶ s₁ ♯ mn ⟩} b Γ≈ = {!!}
≈-base {` ad} {A ∶ s ♯ n} b Γ≈ = {!!}
≈-base {⟨ c , v ⟩at x} {A ∶ s ♯ n} b Γ≈ = {!!}
≈-base {⟨ A has v ⟩at x} {A₁ ∶ s ♯ n} b Γ≈ = {!!}
≈-base {A auth[ a ]} {A₁ ∶ s ♯ n} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {A₁ ∶ s₁ ♯ n} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {A₁ ∶ s₁ ♯ n₁} b Γ≈ = {!!}
≈-base {` ad} {Γ ∣ Γ₁} b Γ≈ = {!!}
≈-base {⟨ c , v ⟩at x} {Γ ∣ Γ₁} b Γ≈ = {!!}
≈-base {⟨ A has v ⟩at x} {Γ ∣ Γ₁} b Γ≈ = {!!}
≈-base {A auth[ a ]} {Γ ∣ Γ₁} b Γ≈ = {!!}
≈-base {⟨ A ∶ s ♯ mn ⟩} {Γ ∣ Γ₁} b Γ≈ = {!!}
≈-base {A ∶ s ♯ n} {Γ ∣ Γ₁} b Γ≈ = {!!}

≈-∣ : ∀ l r →
  ∙ Γ′ ≈ l ∣ r
    ──────────────────
    ∃ λ l′ → ∃ λ r′
      → (l′ ≈ l)
      × (r′ ≈ r)
      × (Γ′ ≈ l′ ∣ r′)
≈-∣ l r = {!!}

deposit∙value : ∀ {A} →
  Γ ≡ ⟨ A has v ⟩at x
  ────────────────────────
  ∀ {x : Id} (x∈ : x ∈ ids Γ) →
    (Γ , x∈) ∙value ≡ v
deposit∙value refl (here refl) = refl

contract∙value :
  Γ ≡ ⟨ c , v ⟩at x
  ────────────────────────
  ∀ {x : Id} (x∈ : x ∈ ids Γ) →
    (Γ , x∈) ∙value ≡ v
contract∙value refl (here refl) = refl

ids↭′ : ∀ (Γ : Cfg) → Γ ↭⦅ ids ⦆ to[ Cfg′ ] Γ
ids↭′ = λ Γ → ↭-reflexive refl

-- toCfg∙value : ∀ (x∈ : x ∈ ids Γ) →
--   (Γ , x∈) ∙value ≡ (to[ Cfg′ ] Γ , L.Perm.∈-resp-↭ (ids↭′ Γ) x∈) ∙value
-- toCfg∙value = ?

∈namesʳ-resp-≈∙value : ∀ (Γ≈ : Γ ≈ Γ′) (x∈ : x ∈ ids Γ) →
  (Γ′ , ∈namesʳ-resp-≈ x {Γ}{Γ′} Γ≈ x∈) ∙value ≡ (Γ , x∈) ∙value
{- ≡ (to[ Cfg′ ] Γ′ , ∈-resp-↭ (ids↭′ Γ) (∈namesʳ-resp-≈ x {Γ}{Γ′} Γ≈ x∈)) ∙value
   ≡ (Γ , x∈) ∙value
-}
∈namesʳ-resp-≈∙value {Γ = ` _}             _ x∈ = contradict x∈
∈namesʳ-resp-≈∙value {Γ = _ auth[ _ ]}     _ x∈ = contradict x∈
∈namesʳ-resp-≈∙value {Γ = ⟨ _ ∶ _ ♯ _ ⟩}   _ x∈ = contradict x∈
∈namesʳ-resp-≈∙value {Γ = _ ∶ _ ♯ _}       _ x∈ = contradict x∈
∈namesʳ-resp-≈∙value {Γ = ⟨ A has v ⟩at x}{Γ′} Γ≈ (here refl)
  = deposit∙value (≈-base {⟨ A has v ⟩at x}{Γ′} tt (↭-sym Γ≈)) _
∈namesʳ-resp-≈∙value {Γ = ⟨ c , v ⟩at x}{Γ′}  Γ≈ (here refl)
  = contract∙value (≈-base {⟨ c , v ⟩at x}{Γ′} tt (↭-sym Γ≈)) _
∈namesʳ-resp-≈∙value {Γ = l ∣ r}           Γ≈ x∈
  -- with l′ , r′ , l≈ , r≈ , Γ≈′
  with destruct-∈-ids-++ l r x∈
... | inj₁ (x∈ˡ , refl) = {!!}
{- GOAL: (Γ′ , ∈namesʳ-resp-≈ x {l ∣ r}{Γ′} Γ≈ (∈-ids-++⁺ˡ x∈ˡ)) ∙value
       ≡ (l′ ∣ r′ , ∈namesʳ-resp-≈ x {l ∣ r}{Γ′} Γ≈ (∈-ids-++⁺ˡ x∈ˡ)) ∙value
       ≡ (l , x∈ˡ) ∙value
       ≡ (l ∣ r , (∈-ids-++⁺ˡ x∈ˡ)) ∙value

  ∈namesʳ-resp-≈∙value {Γ = l} l≈ x∈ˡ
    : (l′ , ∈namesʳ-resp-≈ x {l}{l′} l≈ x∈ˡ) ∙value ≡ (l , x∈ˡ) ∙value
-}
... | inj₂ (x∈ʳ , refl) = {!!}
{- GOAL: (Γ′ , ∈namesʳ-resp-≈ x {l ∣ r}{Γ′} Γ≈ (∈-ids-++⁺ʳ x∈ʳ)) ∙value
       ≡ (l′ ∣ r′ , ∈namesʳ-resp-≈ x {l ∣ r}{Γ′} Γ≈ (∈-ids-++⁺ˡ x∈ˡ)) ∙value
       ≡ (r , x∈ʳ) ∙value
       ≡ (l ∣ r , (∈-ids-++⁺ʳ x∈ʳ)) ∙value

  ∈namesʳ-resp-≈∙value {Γ = r} r≈ x∈ʳ
    : (r′ , ∈namesʳ-resp-≈ x {r}{r′} r≈ x∈ʳ) ∙value ≡ (r , x∈ʳ) ∙value
-}
-- unquoteDecl _∙Run _∙run ∙run=_ = genAccessor _∙Run _∙run ∙run=_ (quote Run)
-- instance
--    ∃ℝ-has-Run : (∃ ℝ) ∙Run
--    ∃ℝ-has-Run = ∙run= proj₁

--    ℝˢ-has-Run : ℝˢ Rˢ ∙Run
--    ℝˢ-has-Run = ∙run= λ where (_⦊_ R {Γ} (𝕒 , _)) → Γ ∷ R ⊣ 𝕒

--    ℝˢ-has-ℝ : HasField′ ℝˢ (ℝ ∘ _∙run)
--    ℝˢ-has-ℝ ._∙ (_ ⦊ _ , 𝕣) = 𝕣
