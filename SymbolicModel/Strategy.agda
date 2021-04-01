-- {-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------
open import Data.List using (length; map; concatMap; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)
import Data.Maybe.Relation.Unary.All as M

open import Prelude.Init hiding (Σ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Collections

module SymbolicModel.Strategy
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes public
open import BitML.Predicate public
  hiding (∣_∣; `)
open import BitML.Contracts Participant Honest public
  hiding (_∙)
open import BitML.Semantics Participant Honest public

-- Symbolic runs.

data Run : Set where
  _∙     : TimedConfiguration → Run
  _∷⟦_⟧_ : TimedConfiguration → Label → Run → Run

infix  6 _∙
infixr 5 _∷⟦_⟧_

variable
  R R′ R″ Rˢ : Run

mapRun : (TimedConfiguration → TimedConfiguration)
       → (Label → Label)
       → Run → Run
mapRun f _ (tc ∙)        = f tc ∙
mapRun f g (tc ∷⟦ α ⟧ s) = f tc ∷⟦ g α ⟧ mapRun f g s

prefixRuns : Run → List Run
prefixRuns (tc ∙)        = [ tc ∙ ]
prefixRuns (tc ∷⟦ α ⟧ R) = let rs = prefixRuns R in rs ++ map (tc ∷⟦ α ⟧_) rs


allTCfgs⁺ : Run → List⁺ TimedConfiguration
allTCfgs⁺ (tc ∙)        = tc ∷ []
allTCfgs⁺ (tc ∷⟦ _ ⟧ r) = tc ∷⁺ allTCfgs⁺ r

allCfgs⁺ : Run → List⁺ Configuration
allCfgs⁺ = L.NE.map cfg ∘ allTCfgs⁺
-- allCfgs⁺ (tc ∙)        = cfg tc ∷ []
-- allCfgs⁺ (tc ∷⟦ _ ⟧ r) = cfg tc ∷⁺ allCfgs⁺ r

allTCfgs : Run → List TimedConfiguration
allTCfgs = L.NE.toList ∘ allTCfgs⁺

allCfgs : Run → List Configuration
allCfgs = map cfg ∘ allTCfgs

-- allCfgs = L.NE.toList ∘ allCfgs⁺

-- allCfgs (tc ∙)        = [ cfg tc ]
-- allCfgs (tc ∷⟦ _ ⟧ r) = cfg tc ∷ allCfgs r

lastCfgᵗ : Run → TimedConfiguration
lastCfgᵗ = L.NE.head ∘ allTCfgs⁺
-- lastCfgᵗ (tc ∙)        = tc
-- lastCfgᵗ (tc ∷⟦ _ ⟧ _) = tc

lastCfg : Run → Configuration
lastCfg = cfg ∘ lastCfgᵗ

-- cfg⟨lastCfgᵗ⟩≡head⟨allCfgs⁺⟩ : cfg (lastCfgᵗ R) ≡ L.NE.head (allCfgs⁺ R)
-- cfg⟨lastCfgᵗ⟩≡head⟨allCfgs⁺⟩ {R = _ ∙}        = refl
-- cfg⟨lastCfgᵗ⟩≡head⟨allCfgs⁺⟩ {R = _ ∷⟦ _ ⟧ _} = refl

-- head∘all≡cfg∘last : L.head (allCfgs R) ≡ just (cfg $ lastCfgᵗ R)
-- head∘all≡cfg∘last {R = _ ∙}        = refl
-- head∘all≡cfg∘last {R = _ ∷⟦ _ ⟧ _} = refl

------------------
-- ** Collections

-- mkCollectʳ : ∀ {X : Set} ⦃ _ : TimedConfiguration has X ⦄ → Run has X
-- mkCollectʳ ⦃ ht ⦄ .collect r with r
-- ... | Γₜ ∙         = collect ⦃ ht ⦄ Γₜ
-- ... | Γₜ ∷⟦ _ ⟧ r′ = collect ⦃ ht ⦄ Γₜ ++ collect ⦃ mkCollectʳ ⦃ ht ⦄ ⦄ r′

instance
  -- Hᵗᶜᶠ⇒Hʳ : ∀ {X : Set} ⦃ _ : TimedConfiguration has X ⦄ → Run has X
  -- -- Hᵗᶜᶠ⇒Hʳ ⦃ ht ⦄ = mkCollectʳ ⦃ ht ⦄
  -- Hᵗᶜᶠ⇒Hʳ ⦃ ht ⦄ .collect = collect ⦃ ht ⦄ ∘ lastCfgᵗ

  HAʳ : Run has Advertisement
  -- HAʳ .collect = mkCollectʳ
  -- HAʳ .collect = authorizedHonAds ∘ cfg ∘ lastCfgᵗ
  HAʳ .collect = concatMap authorizedHonAds ∘ allCfgs

  HNʳ : Run has Name
  -- HNʳ .collect = mkCollectʳ
  HNʳ .collect = collect ∘ lastCfgᵗ

  HSʳ : Run has Secret
  HSʳ .collect = filter₂ ∘ collect {B = Name}

  HLʳ : Run has Label
  HLʳ .collect (_ ∙)        = []
  HLʳ .collect (_ ∷⟦ α ⟧ R) = α ∷ collect R

labels : ∀ {X : Set} → ⦃ _ :  X has Label ⦄ → X → Labels
labels = collect

-- authorizedAds : Run → List Advertisement
-- authorizedAds = concatMap authorizedHonAds ∘ allCfgs

-- ** ancestor advertisement of an active contract

Ancestor : Run → ActiveContract → Advertisement → Set
Ancestor R (c , v , x) ad
  = (c ⊆ subtermsᶜ′ (C ad))
  × (ad ∈ advertisements R)
  × Any ((` ad) ∈ᶜ_) Rᶜ
  × Any (⟨ c , v ⟩at x ∈ᶜ_) Rᶜ
  where Rᶜ = allCfgs R

Ancestor⇒∈ : Ancestor R (c , v , x) ad → c ⊆ subtermsᶜ′ (C ad)
Ancestor⇒∈ = proj₁

Ancestor→𝕂 : Ancestor R (c , v , x) ad → ad ∈ advertisements R
Ancestor→𝕂 = proj₁ ∘ proj₂

-- T0D0: replace with SymbolicModel.Ancestor, with proper provenance


-- Stripping.

record Strippable (A : Set) : Set where
  field
    _∗ : A → A
open Strippable ⦃ ... ⦄ public

instance
  ∗ᶜ : Strippable Configuration
  ∗ᶜ ._∗ c with c
  ... | ⟨ p ∶ a ♯ _ ⟩ = ⟨ p ∶ a ♯ nothing ⟩
  ... | l ∣ r         = l ∗ ∣ r ∗
  ... | _             = c

  ∗ᵗ : Strippable TimedConfiguration
  ∗ᵗ ._∗ (Γ at t) = (Γ ∗) at t

  ∗ˡ : Strippable Label
  ∗ˡ ._∗ l with l
  ... | auth-commit[ p , ad , _ ] = auth-commit[ p , ad , [] ]
  ... | _                         = l

  ∗ʳ : Strippable Run
  ∗ʳ ._∗ = mapRun _∗ _∗

infix -1 _——→[_]_
_——→[_]_ : Run → Label → TimedConfiguration → Set
R ——→[ α ] tc′ = lastCfgᵗ R —→ₜ[ α ] tc′

_∈ʳ_ : Configuration → Run → Set
_∈ʳ_ c R = c ∈ᶜ cfg (lastCfgᵗ (R ∗))

----------------------------------
-- Symbolic strategies.

record ParticipantStrategy (A : Participant) : Set where
  field
    Σ : Run → Labels

    valid : -- participant is honest
            A ∈ Hon
            -- (1) only moves enabled by the semantics
          × (∀ {R α}
             → α ∈ Σ (R ∗)
             → ∃[ R′ ] (R ——→[ α ] R′))
            -- (2) only self-authorizations
          × (∀ {R α}
             → α ∈ Σ (R ∗)
             → M.All (_≡ A) (authDecoration α))
            -- (3) coherent secret lengths
          × (∀ {R ad Δ Δ′}
             → auth-commit[ A , ad , Δ  ] ∈ Σ (R ∗)
             → auth-commit[ A , ad , Δ′ ] ∈ Σ (R ∗)
             → Δ ≡ Δ′)
            -- (4) persistence
          × (∀ {R Γₜ α}
             → α ∈ Σ (R ∗)
             → ∃[ α₁ ] (R ——→[ α₁ ] Γₜ)
             → ∃[ R″ ] (Γₜ ∷⟦ α ⟧ R ——→[ α ] R″)
             → α ∈ Σ ((Γₜ ∷⟦ α ⟧ R) ∗))

open ParticipantStrategy public

HonestStrategies : Set
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A

HonestMoves : Set
HonestMoves = List (Participant × Labels)

variable
  moves : HonestMoves

instance
  ∗ᵐ : Strippable HonestMoves
  ∗ᵐ ._∗ = map (map₂ (map _∗))

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversaryStrategy : Set where
    field
      Σₐ : Run → HonestMoves → Label

      valid :
        ∀ {R moves} →
          let α = Σₐ (R ∗) (moves ∗) in
          ( -- (1) pick from honest moves
            ∃[ A ]
              ( A ∈ Hon
              × authDecoration α ≡ just A
              × α ∈ concatMap proj₂ moves )
            -- (2) independent move
          ⊎ ( authDecoration α ≡ nothing
            × (∀ δ → α ≢ delay[ δ ])
            × ∃[ R′ ] (R ——→[ α ] R′) )
            -- (3) move from dishonest participant
          ⊎ ∃[ B ]
              ( authDecoration α ≡ just B
              × B ∉ Hon
              × (∀ a → α ≢ auth-rev[ B , a ])
              × ∃[ R′ ] (R ——→[ α ] R′) )
            -- (4) delay
          ⊎ ∃[ δ ]
              ( (α ≡ delay[ δ ])
              × All (λ{ (_ , Λ) → (Λ ≡ []) ⊎ Any (λ{ delay[ δ′ ] → δ′ ≥ δ ; _ → ⊥ }) Λ}) moves )
            -- (5) dishonest participant reveals secret
          ⊎ ∃[ B ] ∃[ a ]
              ( α ≡ auth-rev[ B , a ]
              × B ∉ Hon
              × ⟨ B ∶ a ♯ nothing ⟩ ∈ʳ (R ∗)
              × ∃[ R∗ ] ∃[ Δ ] ∃[ ad ]
                  ( R∗ ∈ prefixRuns (R ∗)
                  × Σₐ R∗ [] ≡ auth-commit[ B , ad , Δ ]
                  × Any (λ{ (s , m) → (s ≡ a) × Is-just m }) Δ ))
          )
          × -- commited secrets from adversaries must not depend on the honest moves
          (∀ {B ad Δ}
            → B ∉ Hon
            → α ≡ auth-commit[ B , ad , Δ ]
              -----------------------------
            → α ≡ Σₐ (R ∗) [])

  open AdversaryStrategy public

  Strategies : Set
  Strategies = AdversaryStrategy -- adversarial strategy
             × HonestStrategies  -- participant strategies

  variable
    SS : Strategies

  runHonestAll : Run → HonestStrategies → HonestMoves
  runHonestAll R S = mapWith∈ Hon (λ {A} A∈ → A , Σ (S A∈) (R ∗))

  runAdversary : Strategies → Run → Label
  runAdversary (S† , S) R = Σₐ S† (R ∗) (runHonestAll R S)

  infix -1 _-conforms-to-_
  data _-conforms-to-_ : Run → Strategies → Set where

    base : Initial Γ
           ---------------------------
         → (Γ at 0) ∙ -conforms-to- SS

    step :
      let α = runAdversary SS R in
        R -conforms-to- SS
      → R ——→[ α ] Γₜ
        ----------------------------
      → Γₜ ∷⟦ α ⟧ R -conforms-to- SS
