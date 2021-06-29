open import Prelude.Init hiding (Σ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Collections
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces

module SymbolicModel.Run
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

-- ** export BitML's definition here, once and for all
open import BitML.BasicTypes public
open import BitML.Predicate public
  hiding (∣_∣; `)
open import BitML.Contracts Participant Honest public
  hiding (_∙)
open import BitML.Semantics Participant Honest public
open import BitML.Semantics.Derived Participant Honest public
  using ()
  renaming (h to origin-validAd)

-- Symbolic runs.
data Run : Set where
  _∙     : TimedConfiguration → Run
  _∷⟦_⟧_ : TimedConfiguration → Label → Run → Run

infix  6 _∙
infixr 5 _∷⟦_⟧_

variable
  R R′ R″ Rˢ Rˢ′ Rˢ″ : Run

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

lastCfgᵗ firstCfgᵗ : Run → TimedConfiguration
lastCfgᵗ = L.NE.head ∘ allTCfgs⁺
-- lastCfgᵗ (tc ∙)        = tc
-- lastCfgᵗ (tc ∷⟦ _ ⟧ _) = tc
firstCfgᵗ = L.NE.last ∘ allTCfgs⁺

lastCfg firstCfg : Run → Configuration
lastCfg = cfg ∘ lastCfgᵗ
firstCfg = cfg ∘ firstCfgᵗ

-- cfg⟨lastCfgᵗ⟩≡head⟨allCfgs⁺⟩ : cfg (lastCfgᵗ R) ≡ L.NE.head (allCfgs⁺ R)
-- cfg⟨lastCfgᵗ⟩≡head⟨allCfgs⁺⟩ {R = _ ∙}        = refl
-- cfg⟨lastCfgᵗ⟩≡head⟨allCfgs⁺⟩ {R = _ ∷⟦ _ ⟧ _} = refl

-- head∘all≡cfg∘last : L.head (allCfgs R) ≡ just (cfg $ lastCfgᵗ R)
-- head∘all≡cfg∘last {R = _ ∙}        = refl
-- head∘all≡cfg∘last {R = _ ∷⟦ _ ⟧ _} = refl

infix -1 _——[_]→_
_——[_]→_ : Run → Label → TimedConfiguration → Set
R ——[ α ]→ tc′ = lastCfgᵗ R —[ α ]→ₜ tc′

instance
  𝕍Run : Validable Run
  𝕍Run .Valid = case_of λ where
    (Γₜ ∙) → Initial Γₜ
    (Γₜ ∷⟦ α ⟧ R) → (R ——[ α ]→ Γₜ) × Valid R

  -- Dec-𝕍Run : DecValidable Run

record 𝕍 (A : Set) ⦃ _ : Validable A ⦄ : Set where
  constructor _∶-_
  field
    witness : A
    validity : Valid witness
open 𝕍 public

{-
-- equivalence with traces
first-∷ : firstCfgᵗ (Γₜ ∷⟦ α ⟧ R) ≡ firstCfgᵗ R
first-∷ {R = R} = last-∷ {xs = allTCfgs⁺ R}

-- to : (r : Run) → firstCfgᵗ r —↠ₜ lastCfgᵗ r
-- to (_ ∙) = [] , (_ ∎ₜ)
-- to (Γₜ ∷⟦ α ⟧ r) = {!!}
first⇔initial : Valid R → Initial (firstCfgᵗ R)
first⇔initial {R = _ ∙} vr = vr
first⇔initial {R = Γₜ ∷⟦ α ⟧ R} (_ , vr)
  rewrite first-∷ {Γₜ}{α}{R}
        = first⇔initial {R = R} vr

to' : Valid R → firstCfgᵗ R —↠ₜ lastCfgᵗ R
to' {R = _ ∙} _ = [] , (_ ∎ₜ)
to' {R = Γₜ ∷⟦ α ⟧ R} (R→ , vr)
  -- rewrite first-∷ {Γₜ}{α}{R}
  -- rewrite last-∷ {Γₜ}{α}{R}
  with αs , tr ← to' {R = R} vr
  = (α ∷ αs) , {!!}
  -- = let αs , tr = to' {R = R} vr
  --   in (α ∷ αs) , {!!} -- (? —→ₜ⟨ ? ⟩ {!!} , ? ⊢ tr)

to : 𝕍 Run → Trace _—↠ₜ_
to (R ∶- vr) = λ where
  .start → firstCfgᵗ R
  .end   → lastCfgᵗ R
  .trace → to' {R = R} vr
  .init  → first⇔initial {R = R} vr

from : Trace _—↠ₜ_ → 𝕍 Run
from tr = {!!}
-}

-- data ValidRun : Pred₀ Run where
--   _∙∶-_ : (Γₜ : TimedConfiguration) → Initial (cfg Γₜ) → ValidRun (Γₜ ∙)
--   _∷⟦_⟧_∶-_ : (Γₜ : TimedConfiguration) → (α : Label) → (R : ValidRun Γₜ)
--     → (Γₜ —[ α ]→ₜ lastCfgᵗ ?)
--     → ValidRun (Γₜ ∷⟦ α ⟧ R)

infix 0 _≡⋯_
_≡⋯_ : Run → TimedConfiguration → Set
R ≡⋯ Γ at t = lastCfgᵗ R ≡ Γ at t

-- trace-ad₀ :
--     Valid R
--   → R ≡⋯ (` ad ∣ Γ) at t
--     --————————————————————
--   → Valid ad
-- trace-ad₀ {R = .(((` _) ∣ _) at _) ∙} (() , _) refl
-- trace-ad₀ {R = .(((` _) ∣ _) at _) ∷⟦ α ⟧ R} (R→ , vr) refl = {!trace-ad₀ {R = R} ? refl!}
