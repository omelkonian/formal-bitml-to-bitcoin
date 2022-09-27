------------------------------------------------------------------------
-- Computational strategies.
------------------------------------------------------------------------

open import Prelude.Init hiding (Σ)
open import Prelude.Lists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Ord
open import Prelude.Validity
open import Prelude.ToList
open import Prelude.InferenceRules
open import Prelude.Traces
open import Prelude.Decidable
open import Prelude.Bitstring
open import Prelude.Serializable

open import Bitcoin

module ComputationalModel.Strategy
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : Participant → KeyPair × KeyPair)
  where

Hon : List Participant
Hon = L.NE.toList Honest

allParticipants : List Participant
allParticipants = finList finPart

open import ComputationalModel.KeyPairs Participant keypairs

-- Computational runs.

Message = List ℤ

postulate fromBitstring : Bitstring → Message

encodeMsg : ∀ {A : Set} → ⦃ Serializable A ⦄ → A → List ℤ
encodeMsg = fromBitstring ∘ encode

data Label : Set where
  -- broadcast message
  _→∗∶_ : Participant → Message → Label

  -- append new transaction
  submit : ∃Tx → Label

  -- perform a delay
  delay : Time → Label

  -- send hash request to oracle
  _→O∶_  : Participant → Message → Label

  -- receive hash from oracle
  O→_∶_ : Participant → Message → Label

unquoteDecl DecEq-Label = DERIVE DecEq [ quote Label , DecEq-Label ]

Run    = List Label
Labels = List Label

variable
  m m′ : Message
  R R′ R″ : Run
  λᶜ : Label

strip : Participant → Run → Run
strip A = mapMaybe go
  where
    go : Label → Maybe Label
    go l@(B →O∶  _) = if A == B then just l else nothing
    go l@(O→ B ∶ _) = if A == B then just l else nothing
    go x            = just x

δʳ : Run → Time
δʳ = sum ∘ map δˡ
  where
    δˡ : Label → Time
    δˡ (delay t) = t
    δˡ _         = 0

𝔹 : Run → Blockchain
𝔹 [] = []
𝔹 (l ∷ ls) with l
... | submit tx = (tx at (δʳ ls)) ∷ 𝔹 ls
... | _         = 𝔹 ls

-- For each participant, the coinbase transaction contains an output redeemable with his/her private key.
Coinbase : Pred₀ ∃Tx
Coinbase (_ , _ , tx) =
  ∀ {A} → A ∈ allParticipants →
    (Ctx 1 , (ƛ (versig [ K̂ A ] [ # 0 ])))
    ∈ map (map₂′ validator) (V.toList (outputs tx))

open import Prelude.Enumerable

Finite⇒Enumerable : ∀ {A : Set ℓ} → Finite A → Enumerable A
Finite⇒Enumerable fin = λ where
  .witness → finList fin
  .finite  → λ x →
    let _ , record {f⁻¹ = fromFin; f = toFin; inverse = _ , inv} = fin
     in subst (_∈ finList fin) (inv x)
      $ L.Mem.∈-map⁺ fromFin (L.Mem.∈-allFin $ toFin x)

instance
  Enum-Part : Enumerable Participant
  Enum-Part = Finite⇒Enumerable finPart

  Dec-Coinbase : Coinbase ⁇¹
  Dec-Coinbase {x = i , o , tx} .dec
    with all? (λ A → (Ctx 1 , (ƛ (versig [ K̂ A ] [ # 0 ])))
                   ∈? map (map₂′ validator) (V.toList (outputs tx)))
              allParticipants
  ... | no ¬∀  = no  (¬∀ ∘ L.All.tabulate)
  ... | yes ∀✓ = yes (L.All.lookup ∀✓)

Coinbase? : Decidable¹ Coinbase
Coinbase? ∃tx = dec ⦃ Dec-Coinbase {x = ∃tx} ⦄

-- Initially, all participants broadcast both their public keys.
initialBroadcasts : Labels
initialBroadcasts = map go allParticipants
  module ∣initialBroadcasts∣ where
    go : Participant → Label
    go A = A →∗∶ (Kᵖ A ∷ K̂ᵖ A ∷ [])

instance
  -- An initial run begins with a coinbase transaction and
  -- all appropriate initial broadcasts.
  Initial-Run : HasInitial Run
  Initial-Run .Initial R =
    ∃[ T₀ ] (Coinbase T₀ × (R ≡ (submit T₀ ∷ initialBroadcasts)))

  Dec-Initial-Run : ∀ {R : Run} → Initial R ⁇
  Dec-Initial-Run {[]} .dec = no λ where (_ , ())
  Dec-Initial-Run {(_ →∗∶ _) ∷ _} .dec = no λ where (_ , ())
  Dec-Initial-Run {delay _ ∷ _} .dec = no λ where (_ , ())
  Dec-Initial-Run {(_ →O∶ _) ∷ _} .dec = no λ where (_ , ())
  Dec-Initial-Run {(O→ _ ∶ _) ∷ _} .dec = no λ where (_ , ())
  Dec-Initial-Run {submit T₀ ∷ R} .dec
    with Coinbase? T₀
  ... | no ¬p = no λ where (.T₀ , p , refl) → ¬p p
  ... | yes p
    with R ≟ initialBroadcasts
  ... | no ¬p = no λ where (_ , _ , refl) → ¬p refl
  ... | yes p′ = yes (T₀ , p , cong (submit T₀ ∷_) p′)

  -- A run is valid, when it has an initial run as a prefix.
  Valid-Run : Validable Run
  Valid-Run .Valid R = ∃[ R₀ ] (Initial R₀ × Suffix≡ R₀ R)

data CRun : Set where
  _∎⊣_✓ : ∀ (R : Run) → Initial R → CRun
  _∷_✓ : Label → CRun → CRun

variable Rᶜ Rᶜ′ : CRun

instance
  ToList-CRun : ToList CRun Label
  ToList-CRun .toList = λ where
    (R ∎⊣ _ ✓) → R
    (l ∷ R ✓)  → l ∷ toList R

  Initial-CRun : HasInitial CRun
  Initial-CRun .Initial = Initial ∘ toList
  -- Initial-CRun .Initial = λ where
  --   (_ ∎⊣ _ ✓) → ⊤
  --   (_ ∷ _ ✓)  → ⊥

Valid-CRun : (R : CRun) → Valid (toList R)
Valid-CRun = λ where
  (R ∎⊣ init ✓) → R , init , suffix-refl R
  (l ∷ R ✓)     → let R₀ , init , R⋯ = Valid-CRun R
                  in  R₀ , init , there R⋯

postulate stripᶜ : Participant → CRun → CRun

oracleMessages : Run → Labels
oracleMessages = mapMaybe go
  where
    go : Label → Maybe Label
    go l@(_ →O∶  _) = just l
    go l@(O→ _ ∶ _) = just l
    go _            = nothing

OracleQuery = Participant × Message
OracleReply = Participant × Message
OracleInteraction = Participant × Message × Message

oracleRequests : Participant → Run → List (Label × Label)
oracleRequests A (l@(A′ →O∶ m) ∷ l′@(O→ A″ ∶ hm) ∷ R) with A ≟ A′ | A′ ≟ A″
... | yes _ | yes _      = (l , l′) ∷ oracleRequests A R
... | _     | _          = oracleRequests A R
oracleRequests A (_ ∷ R) = oracleRequests A R
oracleRequests _ []      = []

oracleInteractions : Run → List OracleInteraction
oracleInteractions r = go (L.reverse r) []
  where
    go : Run → List OracleQuery → List OracleInteraction
    go []       ws = []
    go (l ∷ ls) ws
       with l
    ... | A →O∶ m   = go ls ((A , m) ∷ ws)
    ... | O→ A ∶ m′ = case findElem ((_≟ A) ∘ proj₁) ws of λ
      { (just (m , ws′)) → (A , proj₂ m , m′) ∷ go ls ws′
      ; nothing          → go ls ws }
    ... | _         = go ls ws

oracleInteractionsᶜ : CRun → List OracleInteraction
oracleInteractionsᶜ = oracleInteractions ∘ toList

∃[_∋?_] : ∀ (λs : Labels) C → Dec (∃ λ B → (B →∗∶ C) ∈ λs)
∃[ [] ∋? C ] = no λ where (_ , ())
∃[ (submit _ ∷ λs) ∋? C ]
  with ∃[ λs ∋? C ]
... | yes (b , b∈) = yes (b , there b∈)
... | no ∄b = no  λ where (b , there b∈) → ∄b (b , b∈)
∃[ ((A →O∶ m) ∷ λs) ∋? C ]
  with ∃[ λs ∋? C ]
... | yes (b , b∈) = yes (b , there b∈)
... | no ∄b = no  λ where (b , there b∈) → ∄b (b , b∈)
∃[ ((O→ A ∶ m) ∷ λs) ∋? C ]
  with ∃[ λs ∋? C ]
... | yes (b , b∈) = yes (b , there b∈)
... | no ∄b = no  λ where (b , there b∈) → ∄b (b , b∈)
∃[ (delay _ ∷ λs) ∋? C ]
  with ∃[ λs ∋? C ]
... | yes (b , b∈) = yes (b , there b∈)
... | no ∄b = no  λ where (b , there b∈) → ∄b (b , b∈)
∃[ ((B →∗∶ m) ∷ λs) ∋? C ]
  with m ≟ C
... | yes refl = yes (B , here refl)
... | no C≢
  with ∃[ λs ∋? C ]
... | yes (b , b∈) = yes (b , there b∈)
... | no ∄b = no λ where
  (b , here refl) → C≢ refl
  (b , there b∈)  → ∄b (b , b∈)

----------------------------------
-- Computational strategies.


-- Consistent update of the blockchain, in a run where certain components of the transaction have been made public.
_▷ʳ_ : Run → ∃Tx → Set
R ▷ʳ ∃tx =
  let tx = proj₂ (proj₂ ∃tx) in
    (𝔹 R ▷ tx , δʳ R)
  × ∃[ B ] (B →∗∶ [ ∃tx ♯ ] ∈ R)
  × V.All.All (λ i → ∃[ tx′ ] ((submit tx′ ∈ R) × (tx′ ♯ ≡ txId i))) (inputs tx)
  × V.All.All (λ w → ∃[ B ] (B →∗∶ V.toList (proj₂ w) ∈ R)) (wit tx)

record ParticipantStrategy (A : Participant) : Set where
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

HonestStrategies : Set
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A

HonestMoves : Set
HonestMoves = List (Participant × Labels)

variable moves : HonestMoves

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversaryStrategy : Set where
    field
      Σₐ : CRun → HonestMoves → Label

      valid :
        ∀ {R moves} →
          let
            R∗ = stripᶜ Adv R
            α  = Σₐ R∗ moves -- T0D0 should the honest moves be stripped?
          in
          ( -- (1) impersonate another participant
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
              × All (λ{ (_ , Λ) → (Λ ≡ []) ⊎ Any (λ{ (delay δ′) → δ′ ≥ δ ; _ → ⊥ }) Λ}) moves )
          )

  open AdversaryStrategy public

  Strategies : Set
  Strategies = AdversaryStrategy -- adversarial strategy
             × HonestStrategies  -- participant strategies

  variable
    SS : Strategies

  runHonestAll : CRun → HonestStrategies → HonestMoves
  runHonestAll R S = mapWith∈ Hon (λ {A} A∈ → A , Σ (S A∈) (stripᶜ A R))

  runAdversary : Strategies → CRun → Label
  runAdversary (S† , S) R = Σₐ S† (stripᶜ Adv R) (runHonestAll R S)

  infix -1 _-pre-conforms-to-_
  data _-pre-conforms-to-_ : CRun → Strategies → Set where

    base : ∀ {R} →
      Initial R
      ────────────────────────
      R -pre-conforms-to- SS

    step : ∀ {R} →
      let
        (S† , S) = SS
        moves = runHonestAll R S
        Λ = map proj₂ moves
        α = Σₐ S† (stripᶜ Adv R) moves
      in
      ∙ R -pre-conforms-to- SS
      ∙ oracleMessages [ α ] ≡ []
      ∙ concatMap oracleMessages Λ ≡ []
        ───────────────────────────────
        α ∷ R ✓ -pre-conforms-to- SS

    oracle-adv : ∀ {R} {m hm : Message} →
      let
        (S† , S) = SS
        moves = runHonestAll R S
        Λ = map proj₂ moves
        α = Σₐ S† (stripᶜ Adv R) moves
      in
        R -pre-conforms-to- SS
      → α ≡ Adv →O∶ m
      → concatMap oracleMessages Λ ≡ []
      → (∀ {hm′} →
          (Adv →O∶ m , O→ Adv ∶ hm′ ) ∈ oracleRequests Adv (toList R)
          ──────────
          hm ≡ hm′)
        ──────────────────────────────────────────────────────────────
        (Adv →O∶ m) ∷ (O→ Adv ∶ hm) ∷ R ✓ ✓ -pre-conforms-to- SS

    oracle-hon : ∀ {R} {A} {A∈ : A ∈ Hon} {m hm : Message} →
      let
        (_ , S) = SS
        Λ = Σ (S A∈) (stripᶜ A R)
      in
      ∙ R -pre-conforms-to- SS
      ∙ L.head (oracleMessages Λ) ≡ just (Adv →O∶ m)
      ∙ (∀ {hm′} →
           (A →O∶ m , O→ A ∶ hm′ ) ∈ oracleRequests A (toList R)
           ──────────
           hm ≡ hm′)
        ───────────────────────────────────────────────────────
        (A →O∶ m) ∷ (O→ A ∶ hm) ∷ R ✓ ✓ -pre-conforms-to- SS

  infix -1 _-conforms-to-_
  _-conforms-to-_ : CRun → Strategies → Set
  R -conforms-to- SS = ∃[ R′ ] (Prefix≡ (toList R) (toList R′) × (R′ -pre-conforms-to- SS))
