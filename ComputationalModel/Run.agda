------------------------------------------------------------------------
-- Computational runs.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.Lists.Finite
open import Prelude.Lists.Suffix
open import Prelude.Lists.Indexed
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Validity
open import Prelude.ToList
open import Prelude.Traces
open import Prelude.Decidable

open import Bitcoin
open import BitML.BasicTypes using (⋯)

module ComputationalModel.Run
  (⋯ : ⋯) (let open ⋯ ⋯)
  (finPart : Finite Participant)
  (keypairs : Participant → KeyPair × KeyPair)
  where

allParticipants : List Participant
allParticipants = finList finPart

open import ComputationalModel.KeyPairs Participant keypairs
open import ComputationalModel.Serialization

-- ** Labels.

data Label : Type where
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

label≢ : ∀ {A B} → m ≢ m′ → A →∗∶ m ≢ B →∗∶ m′
label≢ m≢ refl = m≢ refl

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

-- For each participant, the coinbase transaction contains an output
-- redeemable with his/her private key.
Coinbase : Pred₀ ∃Tx
Coinbase (_ , _ , tx) =
  ∀ {A} → A ∈ allParticipants →
    (1 , (ƛ (versig [ K̂ A ] [ # 0 ])))
    ∈ map (map₂′ validator) (V.toList (outputs tx))

open import Prelude.Enumerable

Finite⇒Enumerable : ∀ {A : Type ℓ} → Finite A → Enumerable A
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
    with all? (λ A → (1 , (ƛ (versig [ K̂ A ] [ # 0 ])))
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
    go A = A →∗∶ encode (Kᵖ A , K̂ᵖ A)

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

data CRun : Type where
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
oracleRequests A (l@(A′ →O∶ m) ∷ l′@(O→ A″ ∶ hm) ∷ R)
  with A ≟ A′ | A′ ≟ A″
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

-- ** Decision procedures.
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

_∈Hon⇒?_ : ∀ (A : Participant) ms →
  Dec (A ∈ Hon → All (Is-just {A = ℕ}) ms)
A ∈Hon⇒? ms
  with A ∈? Hon
... | no A∉  = yes λ A∈ → ⊥-elim $ A∉ A∈
... | yes A∈
  with all? (M.Any.dec λ _ → yes tt) ms
... | no ¬p = no λ p → ¬p (p A∈)
... | yes p = yes λ _ → p

instance
  Dec-∃B : ∀ {λs : Labels} → (∃ λ B → (B →∗∶ m) ∈ λs) ⁇
  Dec-∃B {m}{λs} .dec = ∃[ λs ∋? m ]

  Dec-∈Hon⇒ : ∀ {A ms} → (A ∈ Hon → All (Is-just {A = ℕ}) ms) ⁇
  Dec-∈Hon⇒ {A}{ms} .dec = A ∈Hon⇒? ms

  Dec-≢-→∗∶ : ∀ {λᶜ}{m} → (∀ A → λᶜ ≢ A →∗∶ m) ⁇
  Dec-≢-→∗∶ {λᶜ}{m} .dec
    with λᶜ in eq
  ... | submit _ = yes λ _ ()
  ... | delay _  = yes λ _ ()
  ... | _ →O∶ _  = yes λ _ ()
  ... | O→ _ ∶ _ = yes λ _ ()
  ... | A →∗∶ m′
    with m ≟ m′
  ... | yes refl = no λ ¬eq → ¬eq A refl
  ... | no m≢    = yes λ where _ refl → m≢ refl
