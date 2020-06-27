------------------------------------------------------------------------
-- Helpers for stripping.
------------------------------------------------------------------------

open import Data.List using (length; map; concatMap; _++_; zip)
open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'

open import BitML.BasicTypes

module SymbolicModel.Helpers
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types                  Participant Honest hiding (c)
open import BitML.Semantics.Action                 Participant Honest
open import BitML.Semantics.Configurations.Types   Participant Honest
open import BitML.Semantics.Configurations.Helpers Participant Honest
open import BitML.Semantics.InferenceRules         Participant Honest
open import BitML.Semantics.Label                  Participant Honest

open import SymbolicModel.Strategy Participant Honest as SM

{-
variable
  Δ : Configuration′ Iᶜᶠ[ [] & rads , [] & [] , [] & [] ]
  Δs : List (Configuration Iᶜᶠ[ [] , [] , [] ])

  R R′ R″ : Run
  T T′ T″ : ∃TimedConfiguration

  c : Contracts ci

  ps : List Participant
  ss : List ValidSecret


strip-cases-helper : ((ci , c) ∷ cs′ ∣∣ᶜˢ Γ) ∗ᶜ
                   ≡ (  ⟨ c ⟩ᶜ
                     ∣∣ (cs′ ∣∣ᶜˢ Γ) ∗ᶜ
                     ∶- refl & refl & refl & (\\-left {[ ci , c ]}) & refl & refl )
strip-cases-helper = refl

strip-cases : (cs′ ∣∣ᶜˢ Γ) ∗ᶜ ≡ (cs′ ∣∣ᶜˢ (Γ ∗ᶜ))
strip-cases {cs′ = []} = refl
strip-cases {cs′ = (ci , c) ∷ cs′} {ads} {cs} {ds} {Γ}
  rewrite strip-cases-helper {ci} {c} {cs′} {ads} {cs} {ds} {Γ}
        | strip-cases {cs′} {ads} {cs} {ds} {Γ}
        = refl

strip-ds : (ds′ ∣∣ᵈˢ Γ) ∗ᶜ ≡ (ds′ ∣∣ᵈˢ Γ ∗ᶜ)
strip-ds {ds′ = []} = refl
strip-ds {ds′ = d ∷ ds′} {Γ = Γ}
  rewrite strip-ds {ds′} {Γ = Γ} = refl

strip-ss : (ss ∣∣ˢˢ Γ) ∗ᶜ ≡ (ss ∣∣ˢˢ Γ ∗ᶜ)
strip-ss {ss = []} = refl
strip-ss {ss = s ∷ ss} {Γ = Γ}
  rewrite strip-ss {ss = ss} {Γ = Γ} = refl

strip-b : ∀ {i j} →
  (Γ ∣∣ᵇ (i , j , ps)) ∗ᶜ ≡ (Γ ∗ᶜ ∣∣ᵇ (i , j , ps))
strip-b {ps = []} = refl
strip-b {ps = p ∷ ps} = strip-b {ps = ps}

strip-committedParticipants : committedParticipants (Γp ∗ᶜ) ad
                            ≡ committedParticipants Γp ad
strip-committedParticipants {Γp = ∅ᶜ}              = refl
strip-committedParticipants {Γp = ` _}             = refl
strip-committedParticipants {Γp = ⟨ _ ⟩ᶜ}          = refl
strip-committedParticipants {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
strip-committedParticipants {Γp = _ auth[ _ ]∶- _} = refl
strip-committedParticipants {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
strip-committedParticipants {Γp = _ ∶ _ ♯ _}       = refl
strip-committedParticipants {Γp = l ∣∣ r ∶- _} {ad = ad}
  rewrite strip-committedParticipants {Γp = l} {ad = ad}
        | strip-committedParticipants {Γp = r} {ad = ad}
        = refl

strip-committedParticipants₂ :
    All (λ p → p ∈ committedParticipants Γp ad)                ps
  → All (λ p → p ∈ committedParticipants (Γp ∗ᶜ) ad) ps
strip-committedParticipants₂ {Γp = Γp} {ad = ad} p
  rewrite strip-committedParticipants {Γp = Γp} {ad = ad} = p

strip-spentForStipulation : spentForStipulation (Γp ∗ᶜ) ad
                          ≡ spentForStipulation Γp ad
strip-spentForStipulation {Γp = ∅ᶜ}              = refl
strip-spentForStipulation {Γp = ` _}             = refl
strip-spentForStipulation {Γp = ⟨ _ ⟩ᶜ}          = refl
strip-spentForStipulation {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
strip-spentForStipulation {Γp = _ auth[ _ ]∶- _} = refl
strip-spentForStipulation {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
strip-spentForStipulation {Γp = _ ∶ _ ♯ _}       = refl
strip-spentForStipulation {Γp = l ∣∣ r ∶- _} {ad = ad}
  rewrite strip-spentForStipulation {Γp = l} {ad = ad}
        | strip-spentForStipulation {Γp = r} {ad = ad}
        = refl

strip-spentForStipulation₂ : toStipulate (G ad) ≡ spentForStipulation Δ ad
                           → toStipulate (G ad) ≡ spentForStipulation (Δ ∗ᶜ) ad
strip-spentForStipulation₂ {ad = ad} {Δ = Δ} p
  rewrite strip-spentForStipulation {Γp = Δ} {ad = ad} = p


open import Data.List.Properties using (map-++-commute)
strip-cfgToList :
  cfgToList (Γp ∗ᶜ) ≡ map (map₂ _∗ᶜ) (cfgToList Γp)
strip-cfgToList {Γp = ∅ᶜ}              = refl
strip-cfgToList {Γp = ` _}             = refl
strip-cfgToList {Γp = ⟨ _ ⟩ᶜ}          = refl
strip-cfgToList {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
strip-cfgToList {Γp = _ auth[ _ ]∶- _} = refl
strip-cfgToList {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
strip-cfgToList {Γp = _ ∶ _ ♯ _}       = refl
strip-cfgToList {Γp = l ∣∣ r ∶- _}
  rewrite strip-cfgToList {Γp = l}
        | strip-cfgToList {Γp = r}
        = sym (map-++-commute (map₂ _∗ᶜ) (cfgToList l) (cfgToList r))

open import Data.List.Relation.Binary.Permutation.Inductive.Properties using (map⁺)
strip-≈ : Γp    ≈ Γp′
        → Γp ∗ᶜ ≈ Γp′ ∗ᶜ
strip-≈ {Γp = Γp} {Γp′ = Γp′} Γp≈
  rewrite strip-cfgToList {Γp = Γp}
        | strip-cfgToList {Γp = Γp′}
        = map⁺ (map₂ _∗ᶜ) Γp≈

strip-lastCfg : lastCfg (R ∗) ≡ (lastCfg R) ∗ᵗ
strip-lastCfg {_ ∙ˢ}        = refl
strip-lastCfg {_ ∷ˢ⟦ _ ⟧ _} = refl

strip-idempotent : ∀ (γ : Configuration′ cf′i) →
  (γ ∗ᶜ) ∗ᶜ ≡ γ ∗ᶜ
strip-idempotent ∅ᶜ                = refl
strip-idempotent (` _)             = refl
strip-idempotent ⟨ _ ⟩ᶜ            = refl
strip-idempotent ⟨ _ , _ ⟩ᵈ        = refl
strip-idempotent (_ auth[ _ ]∶- _) = refl
strip-idempotent ⟨ _ ∶ _ ♯ _ ⟩     = refl
strip-idempotent (_ ∶ _ ♯ _)       = refl
strip-idempotent (l ∣∣ r ∶- _)     rewrite strip-idempotent l
                                        | strip-idempotent r
                                        = refl

strip-strip-rewrite : ∀ {l : Configuration Iᶜᶠ[ ads , cs , ds ]} {γ : Configuration Iᶜᶠ[ ads′ , cs′ , ds′ ]} {pr}
  → (_∣∣_∶-_ {ads = ads ++ ads′} {rads = []}
             {cs = cs  ++ cs′} {rcs = []}
             {ds = ds ++ ds′} {rds = []}
             l ((γ ∗ᶜ) ∗ᶜ) pr)
  ≡ (l ∣∣ γ ∗ᶜ ∶- pr)
strip-strip-rewrite {γ = γ}
  rewrite strip-idempotent γ
        = refl

help : R ∗ ——→[ α ] T′
     → proj₂ ((lastCfg R) ∗ᵗ) —→ₜ[ α ] proj₂ T′
help {R = _ ∙ˢ}        R→ = R→
help {R = _ ∷ˢ⟦ _ ⟧ _} R→ = R→

destruct-γ∗ : ∀ {Γ Γ₀ : Configuration′ Iᶜᶠ[ ads & rads , cs & rcs , ds & rds ]}
                {l    : Configuration Iᶜᶠ[ ads′ , cs′ , ds′ ]}
                {γ∗   : Configuration′ Iᶜᶠ[ adsʳ & radsʳ , csʳ & rcsʳ , dsʳ & rdsʳ ]}
                {pr   : ads  ≡ ads′ ++ adsʳ
                      × rads ≡ [] ++ (radsʳ \\ ads′)
                      × cs   ≡ cs′  ++ csʳ
                      × rcs  ≡ [] ++ (rcsʳ \\ cs′)
                      × ds   ≡ (ds′ \\ rdsʳ) ++ dsʳ
                      × rds  ≡ [] ++ (rdsʳ \\ ds′) }
  → Γ₀ ≡ Γ ∗ᶜ
  → Γ₀ ≡ (l ∗ᶜ ∣∣ γ∗ ∶- pr)
  → ∃[ γ ] ( (γ∗ ≡ γ ∗ᶜ)
           × (Γ ≡ (l ∣∣ γ ∶- pr)) )
destruct-γ∗ {Γ = ∅ᶜ}              refl ()
destruct-γ∗ {Γ = ` _}             refl ()
destruct-γ∗ {Γ = ⟨ _ ⟩ᶜ}          refl ()
destruct-γ∗ {Γ = ⟨ _ , _ ⟩ᵈ}      refl ()
destruct-γ∗ {Γ = _ auth[ _ ]∶- _} refl ()
destruct-γ∗ {Γ = ⟨ _ ∶ _ ♯ _ ⟩}   refl ()
destruct-γ∗ {Γ = _ ∶ _ ♯ _}       refl ()
destruct-γ∗ {Γ = l′ ∣∣ γ ∶- pr₂} {Γ₀ = Γ₀} {l = l} {γ∗ = γ∗} {pr = pr₁} p0 p
  with pr₁
... | (refl , refl , refl , refl , refl , refl)
    = {! γ , refl , refl !}

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

-}
