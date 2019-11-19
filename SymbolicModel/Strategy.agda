------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------

open import Function using (_∘_)

open import Data.Empty   using (⊥)
open import Data.Product using (∃; ∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; map₂; <_,_>; uncurry)
open import Data.Sum     using (_⊎_)
open import Data.Nat     using (ℕ; _>_; _≥_)
open import Data.Maybe   using (Maybe; just; nothing; Is-just)
open import Data.List    using (List; []; _∷_; [_]; length; map; concatMap; _++_)

open import Data.Maybe.Relation.Unary.All using () renaming (All to Allₘ)

open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)
open import Data.List.Relation.Unary.All       using (All)
open import Data.List.Relation.Unary.Any       using (Any)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Prelude.Lists
import Prelude.Set' as SET

open import BitML.BasicTypes

module SymbolicModel.Strategy
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types                  Participant _≟ₚ_ Honest hiding (_∙)
open import BitML.Contracts.DecidableEquality      Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
open import BitML.Semantics.InferenceRules         Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types           Participant _≟ₚ_ Honest

-- Symbolic runs.

data Run : Set where
  _∙     : TimedConfiguration → Run
  _∷⟦_⟧_ : TimedConfiguration → Label → Run → Run

infix  6 _∙
infixr 5 _∷⟦_⟧_

variable
  R R′ R″ : Run

mapRun : (TimedConfiguration → TimedConfiguration)
       → (Label → Label)
       → Run → Run
mapRun f _ (tc ∙)        = f tc ∙
mapRun f g (tc ∷⟦ α ⟧ s) = f tc ∷⟦ g α ⟧ mapRun f g s

lastCfg : Run → TimedConfiguration
lastCfg (tc ∙)        = tc
lastCfg (tc ∷⟦ _ ⟧ _) = tc

prefixRuns : Run → List Run
prefixRuns (tc ∙)        = [ tc ∙ ]
prefixRuns (tc ∷⟦ α ⟧ R) = let rs = prefixRuns R in rs ++ map (tc ∷⟦ α ⟧_) rs

-- Stripping.

_∗ᶜ : Configuration → Configuration
⟨ p ∶ a ♯ _ ⟩ ∗ᶜ = ⟨ p ∶ a ♯ nothing ⟩
(l ∣ r)       ∗ᶜ = l ∗ᶜ ∣ r ∗ᶜ
c             ∗ᶜ = c

_∗ᵗ : TimedConfiguration → TimedConfiguration
(Γ at t) ∗ᵗ = (Γ ∗ᶜ) at t

_✴ˡ : Label → Label
_✴ˡ auth-commit[ p , ad , _ ] = auth-commit[ p , ad , [] ]
_✴ˡ a = a

-- Hide all committed secrets in a symbolic run.
_∗ : Run → Run
_∗ = mapRun _∗ᵗ _✴ˡ

infix -1 _——→[_]_
_——→[_]_ : Run → Label → TimedConfiguration → Set
R ——→[ α ] tc′ = lastCfg R —→ₜ[ α ] tc′

_∈ʳ_ : Configuration → Run → Set
_∈ʳ_ c R = c ∈ cfgToList (cfg (lastCfg (R ∗)))

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
             → Allₘ (_≡ A) (authDecoration α))
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

_✴ᵐ : HonestMoves → HonestMoves
_✴ᵐ = map (map₂ (map _✴ˡ))

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversaryStrategy : Set where
    field
      Σₐ : Run → HonestMoves → Label

      valid :
        ∀ {R moves} →
          let α = Σₐ (R ∗) (moves ✴ᵐ) in
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
