------------------------------------------------------------------------
-- Computational strategies.
------------------------------------------------------------------------
open import Prelude.Init hiding (Σ); open SetAsType
open import Prelude.Lists.Finite
open import Prelude.Lists.Prefix
open import Prelude.Membership
open import Prelude.Ord
open import Prelude.Validity
open import Prelude.ToList
open import Prelude.InferenceRules
open import Prelude.Traces
open import Prelude.Null

open import Bitcoin
open import BitML.BasicTypes using (⋯)

module ComputationalModel.Strategy
  (⋯ : ⋯) (let open ⋯ ⋯)
  (finPart : Finite Participant)
  (keypairs : Participant → KeyPair × KeyPair)
  where

open import ComputationalModel.KeyPairs Participant keypairs
open import ComputationalModel.Serialization
open import ComputationalModel.Run ⋯ finPart keypairs

-- Consistent update of the blockchain, in a run where certain
-- components of the transaction have been made public.
_▷ʳ_ : Run → ∃Tx → Type
R ▷ʳ ∃tx =
  let tx = proj₂ (proj₂ ∃tx) in
    (𝔹 R ▷ tx , δʳ R)
  × ∃[ B ] (B →∗∶ (∃tx ♯) ∈ R)
  × V.All.All (λ i → ∃[ tx′ ] ((submit tx′ ∈ R) × (tx′ ♯ ≡ txId i)))
              (inputs tx)
  × V.All.All (λ w → ∃[ B ] (B →∗∶ encode (V.toList (proj₂ w)) ∈ R)) (wit tx)

record ParticipantStrategy (A : Participant) : Type where
  field Σ : CRun → Labels
open ParticipantStrategy public

instance
  Valid-Strategy : ∀ {A} → Validable (ParticipantStrategy A)
  Valid-Strategy {A = A} .Valid (record {Σ = Σ}) =
      -- participant is honest
      A ∈ Hon
      -- only valid computational labels
    × (∀ {R α} → let R∗ = stripᶜ A R in
          α ∈ Σ R∗
        → ( -- (1) message from A
            ∃[ m ]
              ( (α ≡ A →∗∶ m)
              ⊎ (α ≡ A →O∶ m) )
            -- (2) new transaction
          ⊎ ∃[ tx ]
              ( (α ≡ submit tx)
              × (toList R∗ ▷ʳ tx) )
            -- (3) delay
          ⊎ ∃[ δ ] (α ≡ delay δ)
          ))
      -- persistence
    × (∀ {R α}
        → let
            R∗ = stripᶜ A R
            Λ  = Σ R∗
            R′ = α ∷ R∗ ✓
            Λ′ = Σ R′
          in
          α ∈ Λ
        → ConsistentBlockchain (𝔹 $ toList R′)
        → (∀ {α′} → α′ ∈ Λ → α′ ≢ α → α′ ∈ Λ′)
        -- → (∀ {tx} → submit tx ∈ Λ → 𝔹 R′ → submit tx ∈ Λ′)
        -- × (∀ {m} → (A →∗∶ m) ∈ Λ → (A →∗∶ m) ≢ α → (A →∗∶ m) ∈ Λ′)
        -- × (∀ {m} → (A →O∶ m) ∈ Λ → (A →O∶ m) ≢ α → (A →O∶ m) ∈ Λ′)
      )

HonestStrategies : Type
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A

HonestMoves : Type
HonestMoves = List (Participant × Labels)

variable moves : HonestMoves

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversaryStrategy : Type where
    field
      Σₐ : CRun → HonestMoves → Label

      valid : ∀ {R moves} →
        let
          R∗ = stripᶜ Adv R
          α  = Σₐ R∗ moves -- T0D0 should the honest moves be stripped?
        in
          -- (1) impersonate another participant
          ∃[ m ]
            ( ∃[ A ] (α ≡ A →∗∶ m)
            ⊎ (α ≡ Adv →O∶ m) )
          -- (2) consistently update the blockchain
        ⊎ ∃[ tx ]
            ( (α ≡ submit tx)
            × (toList R∗ ▷ʳ tx) )
          -- (3) delay, if all honest participants agree
        ⊎ ∃[ δ ]
            ( (α ≡ delay δ)
            × All (λ{ (_ , Λ) →
              (Λ ≡ []) ⊎
              Any (λ{ (delay δ′) → δ′ ≥ δ ; _ → ⊥ }) Λ}
            ) moves
            )

  open AdversaryStrategy public

  Strategies : Type
  Strategies = AdversaryStrategy -- adversarial strategy
             × HonestStrategies  -- participant strategies

  variable
    SS : Strategies

  runHonestAll : CRun → HonestStrategies → HonestMoves
  runHonestAll R S = mapWith∈ Hon (λ {A} A∈ → A , Σ (S A∈) (stripᶜ A R))

  runAdversary : Strategies → CRun → Label
  runAdversary (S† , S) R = Σₐ S† (stripᶜ Adv R) (runHonestAll R S)

  infix -1 _⋯∼ᶜ_ _∼ᶜ_

  data _⋯∼ᶜ_ : CRun → Strategies → Type where
    -- (1)
    base : ∀ {R} →
      Initial R
      ─────────
      R ⋯∼ᶜ SS
    -- (2)
    step : ∀ {R} →
      let
        (S† , S) = SS
        moves = runHonestAll R S
        Λ = map proj₂ moves
        α = Σₐ S† (stripᶜ Adv R) moves
      in
      ∙ R ⋯∼ᶜ SS
      ∙ Null (oracleMessages [ α ])
      ∙ Null (concatMap oracleMessages Λ)
        ─────────────────────────────────
        α ∷ R ✓ ⋯∼ᶜ SS
    -- (3)
    oracle-adv : ∀ {R} {m hm : Message} →
      let
        (S† , S) = SS
        moves = runHonestAll R S
        Λ = map proj₂ moves
        α = Σₐ S† (stripᶜ Adv R) moves
      in
      ∙ R ⋯∼ᶜ SS
      ∙ α ≡ Adv →O∶ m
      ∙ Null (concatMap oracleMessages Λ)
      ∙ (∀ {hm′} →
          (Adv →O∶ m , O→ Adv ∶ hm′) ∈ oracleRequests Adv (R ∙toList)
          ───────────────────────────────────────────────────────────
          hm ≡ hm′)
        ──────────────────────────────────────────
        (Adv →O∶ m) ∷ (O→ Adv ∶ hm) ∷ R ✓ ✓ ⋯∼ᶜ SS
    -- (4)
    oracle-hon : ∀ {R} {A} {A∈ : A ∈ Hon} {m hm : Message} →
      let
        (_ , S) = SS
        Λ = Σ (S A∈) (stripᶜ A R)
      in
      ∙ R ⋯∼ᶜ SS
      ∙ L.head (oracleMessages Λ) ≡ just (Adv →O∶ m)
      ∙ (∀ {hm′} →
          (A →O∶ m , O→ A ∶ hm′ ) ∈ oracleRequests A (R ∙toList)
          ──────────
          hm ≡ hm′)
        ─────────────────────────────────────────────────────────
        (A →O∶ m) ∷ (O→ A ∶ hm) ∷ R ✓ ✓ ⋯∼ᶜ SS

  _∼ᶜ_ : CRun → Strategies → Type
  R ∼ᶜ SS = ∃[ R′ ] (Prefix≡ (toList R) (toList R′) × (R′ ⋯∼ᶜ SS))
