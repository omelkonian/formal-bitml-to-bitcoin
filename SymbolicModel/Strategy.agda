------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------
open import Prelude.Init hiding (Σ); open SetAsType
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Bifunctor
open import Prelude.Ord
open import Prelude.Traces
open import Prelude.InferenceRules

open import BitML.BasicTypes using (⋯)

module SymbolicModel.Strategy (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯ public
open import SymbolicModel.Stripping ⋯ public

record ParticipantStrategy (A : Participant) : Type where
  field Σ : Run → Labels
open ParticipantStrategy public

instance
  Valid-Strategy : Validable (ParticipantStrategy A)
  Valid-Strategy {A = A} .Valid (record {Σ = Σ}) =
      -- participant is honest
      A ∈ Hon
      -- (1) only moves enabled by the semantics
    × (∀ {R α}
       → α ∈ Σ (R ∗)
       → ∃ (R ——[ α ]→_))
      -- (2) only self-authorizations
    × (∀ {R α}
       → α ∈ Σ (R ∗)
       → M.All.All (_≡ A) (authDecoration α))
      -- (3) coherent secret lengths
    × (∀ {R ad Δ Δ′}
       → auth-commit⦅ A , ad , Δ  ⦆ ∈ Σ (R ∗)
       → auth-commit⦅ A , ad , Δ′ ⦆ ∈ Σ (R ∗)
       → Δ ≡ Δ′)
      -- (4) persistence
    × (∀ {R : Run} {Γₜ} {α : Label}
       → α ∈ Σ (R ∗)
       → ∃[ α₁ ] (R ——[ α₁ ]→ Γₜ)
       )
       -- → ∃[ R″ ] (Γₜ ∷⟦ α ⟧ R ——[ α ]→ R″)
       -- → α ∈ Σ ((Γₜ ∷⟦ α ⟧ R) ∗))

HonestStrategies : Type
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A

HonestMoves : Type
HonestMoves = List (Participant × Labels)

variable
  moves : HonestMoves

instance
  ∗ᵐ : Strippable HonestMoves
  ∗ᵐ ._∗ = map (map₂ (map _∗))

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversaryStrategy : Type where
    field Σₐ : Run → HonestMoves → Label
  open AdversaryStrategy public

  instance
    Valid-AdversaryStrategy : Validable AdversaryStrategy
    Valid-AdversaryStrategy .Valid (record {Σₐ = Σₐ}) =
        ∀ {R moves} →
          let α = Σₐ (R ∗) (moves ∗) in
          ( -- (1) pick from honest moves
            ∃[ A ]
              ( A ∈ Hon
              × authDecoration α ≡ just A
              × α ∈ concatMap proj₂ moves )
            -- (2) independent move
          ⊎ ( authDecoration α ≡ nothing
            × (∀ δ → α ≢ delay⦅ δ ⦆)
            × ∃[ R′ ] (R ——[ α ]→ R′) )
            -- (3) move from dishonest participant
          ⊎ ∃[ B ]
              ( authDecoration α ≡ just B
              × B ∉ Hon
              × (∀ a → α ≢ auth-rev⦅ B , a ⦆)
              × ∃[ R′ ] (R ——[ α ]→ R′) )
            -- (4) delay
          ⊎ ∃[ δ ]
              ( (α ≡ delay⦅ δ ⦆)
              × All (λ{ (_ , Λ) → (Λ ≡ []) ⊎ Any (λ{ delay⦅ δ′ ⦆ → δ′ ≥ δ ; _ → ⊥ }) Λ}) moves )
            -- (5) dishonest participant reveals secret
          ⊎ ∃[ B ] ∃[ a ]
              ( (α ≡ auth-rev⦅ B , a ⦆)
              × (B ∉ Hon)
              × (⟨ B ∶ a ♯ nothing ⟩ ∈ᶜ (R ∗) .end .cfg)
              × (∃[ R∗ ] ∃[ Δ ] ∃[ ad ]
                  ( R∗ ∈ prefixRuns (R ∗)
                  × Σₐ R∗ [] ≡ auth-commit⦅ B , ad , Δ ⦆
                  × Any (λ{ (s , m) → (s ≡ a) × Is-just m }) Δ )))
          )
          × -- commited secrets from adversaries must not depend on the honest moves
          (∀ {B ad Δ}
            → B ∉ Hon
            → α ≡ auth-commit⦅ B , ad , Δ ⦆
              -----------------------------
            → α ≡ Σₐ (R ∗) [])

  Strategies : Type
  Strategies = AdversaryStrategy -- adversarial strategy
             × HonestStrategies  -- participant strategies

  variable
    SS : Strategies

  runHonestAll : Run → HonestStrategies → HonestMoves
  runHonestAll R S = mapWith∈ Hon (λ {A} A∈ → A , Σ (S A∈) (R ∗))

  runAdversary : Strategies → Run → Label
  runAdversary (S† , S) R = Σₐ S† (R ∗) (runHonestAll R S)

  infix -1 _∼ˢ_
  data _∼ˢ_ : Run → Strategies → Type where

    base :
      ∀ (init : Initial Γ) →
        ───────────────────────────────
        (Γ at 0) ∎⊣ (init , refl) ∼ˢ SS

    step : let α = runAdversary SS R in
      ∙ R ∼ˢ SS
      → (R→ : R ——[ α ]→ Γₜ) →
        ─────────────────────────
        (Γₜ ⟨ R→ ⟩←—— R ⊣≡) ∼ˢ SS
