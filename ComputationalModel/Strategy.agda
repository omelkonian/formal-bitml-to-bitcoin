------------------------------------------------------------------------
-- Computational strategies.
------------------------------------------------------------------------

open import Function using (_∘_; _∋_)

open import Data.Empty        using (⊥)
open import Data.Unit         using (⊤)
open import Data.Product      using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂; map₂)
open import Data.Sum          using (_⊎_)
open import Data.Nat          using (ℕ; _>_; _≥_)
open import Data.Integer      using (ℤ)
open import Data.Fin          using (Fin)
open import Data.Fin.Patterns using (0F)
open import Data.Maybe        using (Maybe; just; nothing)
open import Data.List         using (List; []; _∷_; [_]; length; map; concatMap; sum; mapMaybe; unzip; head)
import Data.Vec as V


open import Data.List.Membership.Propositional              using (_∈_; _∉_; mapWith∈)
open import Data.List.Relation.Permutation.Inductive        using (_↭_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous  using (Prefix)
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All                    using (All)
open import Data.List.Relation.Unary.Any                    using (Any)

open import Data.Vec.Relation.Unary.All using ()
  renaming (All to Allᵥ)

open import Data.Maybe.Relation.Unary.All using ()
  renaming (All to Allₘ)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Prelude.Lists
import Prelude.Set' as SET

open import Bitcoin.Crypto                using (KeyPair; pub; sec)
open import Bitcoin.BasicTypes            using (Time)
open import Bitcoin.Script.Base           using (ƛ_; versig; Ctx)
open import Bitcoin.Tx.Base               using (∃Tx; outputs; inputs; wit; _at_; validator; txId)
open import Bitcoin.Tx.Crypto             using (hashTx)
open import Bitcoin.Semantics.Consistency using (Blockchain; _▷_,_; ConsistentBlockchain)

-- open import BitML.BasicTypes

module ComputationalModel.Strategy
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)
  where

Hon : List Participant
Hon = proj₁ Honest

allParticipants : List Participant
allParticipants = finList finPart

-- Key pairs.
K : Participant → KeyPair
K = proj₁ ∘ keypairs

K̂ : Participant → KeyPair
K̂ = proj₂ ∘ keypairs

Kᵖ : Participant → ℤ
Kᵖ = pub ∘ K

K̂ᵖ : Participant → ℤ
K̂ᵖ = pub ∘ K̂

-- Computational runs.

Message = List ℤ

data Label : Set where
  -- broadcast message
  _→✴∶_ : Participant → Message → Label

  -- append new transaction
  submit : ∃Tx → Label

  -- perform a delay
  delay : Time → Label

  -- send hash request to oracle
  _→O∶_  : Participant → Message → Label

  -- receive hash from oracle
  O→_∶_ : Participant → Message → Label

Run    = List Label
Labels = List Label

variable
  R R′ R″ : Run

strip : Participant → Run → Run
strip A = mapMaybe go
  where
    go : Label → Maybe Label
    go l@(B →O∶  _) with A ≟ₚ B
    ... | yes _ = just l
    ... | no  _ = nothing
    go l@(O→ B ∶ _) with A ≟ₚ B
    ... | yes _ = just l
    ... | no  _ = nothing
    go x = just x

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
Coinbase : ∃Tx → Set
Coinbase (_ , _ , tx) =
  ∀ {A} → A ∈ allParticipants →
    (Ctx 1 , (ƛ (versig [ K̂ A ] [ 0F ]))) ∈ map (map₂ validator) (V.toList (outputs tx))

-- Initially, all participants broadcast both their public keys.
initialBroadcasts : Labels
initialBroadcasts = map go allParticipants
  where
    go : Participant → Label
    go A = A →✴∶ (Kᵖ A ∷ K̂ᵖ A ∷ [])

-- An initial run begins with a coinbase transaction and all appropriate initial broadcasts.
Initial : Run → Set
Initial R = ∃[ T₀ ] (Coinbase T₀ × (R ↭ (submit T₀ ∷ initialBroadcasts)))

-- A run is valid, when it has an initial run as a prefix.
Valid : Run → Set
Valid R = ∃[ R₀ ] (Initial R₀ × Prefix _≡_ R₀ R)

----------------------------------
-- Computational strategies.


-- Consistent update of the blockchain, in a run where certain components of the transaction have been made public.
_▷ʳ_ : Run → ∃Tx → Set
R ▷ʳ ∃tx =
  let tx = proj₂ (proj₂ ∃tx) in
    (𝔹 R ▷ tx , δʳ R)
  × ∃[ B ] (B →✴∶ [ hashTx ∃tx ] ∈ R)
  × Allᵥ (λ i → ∃[ tx′ ] ((submit tx′ ∈ R) × (hashTx tx′ ≡ txId i))) (inputs tx)
  × Allᵥ (λ w → ∃[ B ] (B →✴∶ V.toList (proj₂ w) ∈ R)) (wit tx)

record ParticipantStrategy (A : Participant) : Set where
  field
    Σ : Run → Labels

    valid : -- participant is honest
            A ∈ Hon
            -- only valid computational labels
          × (∀ {R α} → let R✴ = strip A R in
               α ∈ Σ R✴
             → ( -- (1) message from A
                 ∃[ m ]
                   ( (α ≡ A →✴∶ m)
                   ⊎ (α ≡ A →O∶ m) )
                 -- (2) new transaction
               ⊎ ∃[ tx ]
                    ( (α ≡ submit tx)
                    × (R✴ ▷ʳ tx) )
                 -- (3) delay
               ⊎ ∃[ δ ] (α ≡ delay δ)
               )
            )
            -- persistence
          × (∀ {R α}
             → let
                 R✴ = strip A R
                 Λ  = Σ R✴
                 R′ = α ∷ R✴
                 Λ′ = Σ R′
               in
               α ∈ Λ
             → ConsistentBlockchain (𝔹 R′)
             → (∀ {α′} → α′ ∈ Λ → α′ ≢ α → α′ ∈ Λ′)
             -- → (∀ {tx} → submit tx ∈ Λ → 𝔹 R′ → submit tx ∈ Λ′)
             -- × (∀ {m} → (A →✴∶ m) ∈ Λ → (A →✴∶ m) ≢ α → (A →✴∶ m) ∈ Λ′)
             -- × (∀ {m} → (A →O∶ m) ∈ Λ → (A →O∶ m) ≢ α → (A →O∶ m) ∈ Λ′)
            )

open ParticipantStrategy public


HonestStrategies : Set
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A

HonestMoves : Set
HonestMoves = List (Participant × Labels)

variable
  moves : HonestMoves

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversaryStrategy : Set where
    field
      Σₐ : Run → HonestMoves → Label

      valid :
        ∀ {R moves} →
          let
            R✴ = strip Adv R
            α  = Σₐ R✴ moves -- T0D0 should the honest moves be stripped?
          in
          ( -- (1) impersonate another participant
            ∃[ m ]
              ( ∃[ A ] (α ≡ A →✴∶ m)
              ⊎ (α ≡ Adv →O∶ m) )
            -- (2) consistently update the blockchain
          ⊎ ∃[ tx ]
              ( (α ≡ submit tx)
              × (R✴ ▷ʳ tx) )
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

  runHonestAll : Run → HonestStrategies → HonestMoves
  runHonestAll R S = mapWith∈ Hon (λ {A} A∈ → A , Σ (S A∈) (strip A R))

  runAdversary : Strategies → Run → Label
  runAdversary (S† , S) R = Σₐ S† (strip Adv R) (runHonestAll R S)

  oracleMessages : Labels → Labels
  oracleMessages = mapMaybe go
    where
      go : Label → Maybe Label
      go l@(_ →O∶  _) = just l
      go l@(O→ _ ∶ _) = just l
      go _            = nothing

  oracleRequests : Participant → Run → List (Label × Label)
  oracleRequests A (l@(A′ →O∶ m) ∷ l′@(O→ A″ ∶ hm) ∷ R) with A ≟ₚ A′ | A′ ≟ₚ A″
  ... | yes _ | yes _      = (l , l′) ∷ oracleRequests A R
  ... | _     | _          = oracleRequests A R
  oracleRequests A (_ ∷ R) = oracleRequests A R
  oracleRequests _ []      = []

  infix -1 _-pre-conforms-to-_
  data _-pre-conforms-to-_ : Run → Strategies → Set where

    base : Initial R
           ----------------------
         → R -pre-conforms-to- SS

    step :
      let
        (S† , S) = SS
        moves = runHonestAll R S
        Λ = map proj₂ moves
        α = Σₐ S† (strip Adv R) moves
      in
        R -pre-conforms-to- SS
      → oracleMessages [ α ] ≡ []
      → concatMap oracleMessages Λ ≡ []
        -------------------------------
      → α ∷ R -pre-conforms-to- SS

    oracle-adv : ∀ {m hm : Message} →
      let
        (S† , S) = SS
        moves = runHonestAll R S
        Λ = map proj₂ moves
        α = Σₐ S† (strip Adv R) moves
      in
        R -pre-conforms-to- SS
      → α ≡ Adv →O∶ m
      → concatMap oracleMessages Λ ≡ []
      → (∀ {hm′} → (Adv →O∶ m , O→ Adv ∶ hm′ ) ∈ oracleRequests Adv R
                 → hm ≡ hm′)
        -------------------------------------------------------------
      → (Adv →O∶ m) ∷ (O→ Adv ∶ hm) ∷ R -pre-conforms-to- SS

    oracle-hon : ∀ {A} {A∈ : A ∈ Hon} {m hm : Message} →
      let
        (_ , S) = SS
        Λ = Σ (S A∈) (strip A R)
      in
        R -pre-conforms-to- SS
      → head (oracleMessages Λ) ≡ just (Adv →O∶ m)
      → (∀ {hm′} → (A →O∶ m , O→ A ∶ hm′ ) ∈ oracleRequests A R
                 → hm ≡ hm′)
        -------------------------------------------------------
      → (A →O∶ m) ∷ (O→ A ∶ hm) ∷ R -pre-conforms-to- SS

  infix -1 _-conforms-to-_
  _-conforms-to-_ : Run → Strategies → Set
  R -conforms-to- SS = ∃[ R′ ] (Prefix _≡_ R R′ × (R′ -pre-conforms-to- SS))
