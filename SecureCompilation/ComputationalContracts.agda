open import Prelude.Init hiding (T)
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Serializable
open import Prelude.Views


open import Bitcoin using (TxInput′)

module SecureCompilation.ComputationalContracts
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel Participant Honest hiding (A; B; begin_; _∎; Σ; _▷_)


-- T0D0: move to Prelude.Lists.MapMaybe
private variable A : Set ℓ; B : Set ℓ′

mapMaybeIsInj₁∘mapInj₁ : (xs : List A) → mapMaybe (isInj₁ {B = B}) (map inj₁ xs) ≡ xs
mapMaybeIsInj₁∘mapInj₁ = λ where
  [] → refl
  (x ∷ xs) → cong (x ∷_) (mapMaybeIsInj₁∘mapInj₁ xs)

mapMaybeIsInj₁∘mapInj₂ : (xs : List B) → mapMaybe (isInj₁ {A = A}) (map inj₂ xs) ≡ []
mapMaybeIsInj₁∘mapInj₂ = λ where
  [] → refl
  (x ∷ xs) → mapMaybeIsInj₁∘mapInj₂ xs

mapMaybeIsInj₂∘mapInj₂ : (xs : List B) → mapMaybe (isInj₂ {A = A}) (map inj₂ xs) ≡ xs
mapMaybeIsInj₂∘mapInj₂ = λ where
  [] → refl
  (x ∷ xs) → cong (x ∷_) (mapMaybeIsInj₂∘mapInj₂ xs)

mapMaybeIsInj₂∘mapInj₁ : (xs : List A) → mapMaybe (isInj₂ {B = B}) (map inj₁ xs) ≡ []
mapMaybeIsInj₂∘mapInj₁ = λ where
  [] → refl
  (x ∷ xs) → mapMaybeIsInj₂∘mapInj₁ xs

-- ** Computational contracts (transaction outputs instead of identifiers)
Idᶜ  = TxInput′
Idsᶜ = List Idᶜ

data Contractᶜ : Set
Contractsᶜ  = List Contractᶜ
VContractsᶜ = List (Value × Contractsᶜ)

data Contractᶜ where
  put_&reveal_if_⇒_ : Idsᶜ → Secrets → Predicate → Contractsᶜ → Contractᶜ
  withdraw : Participant → Contractᶜ
  split : VContractsᶜ → Contractᶜ
  _⇒_ : Participant → Contractᶜ → Contractᶜ
  after_⇒_ : Time → Contractᶜ → Contractᶜ

data Preconditionᶜ : Set where
  _:?_at_ : Participant → Value → Idᶜ → Preconditionᶜ
  _:!_at_ : Participant → Value → Idᶜ → Preconditionᶜ
  _:secret_ : Participant → Secret → Preconditionᶜ
  _∣∣_ : Preconditionᶜ → Preconditionᶜ → Preconditionᶜ

record Advertisementᶜ : Set where
  constructor ⟨_⟩_
  field
    G : Preconditionᶜ
    C : Contractsᶜ

infix  2 ⟨_⟩_

infix  5 _:?_at_
infix  5 _:!_at_
infix  5 _:secret_
infixl 2 _∣∣_

infixr 9 _⇒_
infix  8 put_&reveal_if_⇒_

private variable X : Set ℓ; Y : Set ℓ′
postulate TODO : X
instance
  postulate
    Serializable-List : ⦃ Serializable X ⦄ → Serializable (List X)
    Serializable-× : ⦃ Serializable X ⦄ → ⦃ Serializable Y ⦄ → Serializable (X × Y)
    Serializable-Value : Serializable Value
    Serializable-Contractᶜ : Serializable Contractᶜ
    Serializable-Preconditionᶜ : Serializable Preconditionᶜ
    Serializable-Advertisementᶜ : Serializable Advertisementᶜ

{- simply-typed version with functions)
module _ (txout : Id → Idᶜ) where
  rei : Contract → Contractᶜ
  reis : Contracts → Contractsᶜ
  reis = λ where
    [] → []
    (c ∷ cs) → rei c ∷ reis cs
  reiss : VContracts → VContractsᶜ
  reiss = λ where
    [] → []
    ((v , cs) ∷ vcs) → (v , reis cs) ∷ reiss vcs
  rei = λ where
    (put xs &reveal as if p ⇒ cs) →
      put (txout <$> xs) &reveal as if p ⇒ reis cs
    (withdraw p) →
      withdraw p
    (split vcs) →
      split (reiss vcs)
    (p ⇒ c) →
      p ⇒ rei c
    (after t ⇒ c) →
      after t ⇒ rei c

module _ (txout⁻¹ : Idᶜ → Id) where
  abs : Contractᶜ → Contract
  abss : Contractsᶜ → Contracts
  abss = λ where
    [] → []
    (c ∷ cs) → abs c ∷ abss cs
  absss : VContractsᶜ → VContracts
  absss = λ where
    [] → []
    ((v , cs) ∷ vcs) → (v , abss cs) ∷ absss vcs
  abs = λ where
    (put xs &reveal as if p ⇒ cs) →
      put (txout⁻¹ <$> xs) &reveal as if p ⇒ abss cs
    (withdraw p) →
      withdraw p
    (split vcs) →
      split (absss vcs)
    (p ⇒ c) →
      p ⇒ abs c
    (after t ⇒ c) →
      after t ⇒ abs c
-}

ids-put≡ : ∀ {xs as} (p : Predicate) (cs : Contracts) →
  ids (Contract ∋ put xs &reveal as if p ⇒ cs) ≡ xs ++ ids cs
ids-put≡ {xs}{as} p cs =
  begin
    ids (Contract ∋ put xs &reveal as if p ⇒ cs)
  ≡⟨⟩
    mapMaybe isInj₂ (map inj₂ xs ++ map inj₁ as ++ names cs)
  ≡⟨ mapMaybe-++ isInj₂ (map inj₂ xs) _ ⟩
    mapMaybe isInj₂ (map inj₂ xs) ++ mapMaybe isInj₂ (map inj₁ as ++ names cs)
  ≡⟨ cong (_++ _) $ mapMaybeIsInj₂∘mapInj₂ xs ⟩
    xs ++ mapMaybe isInj₂ (map inj₁ as ++ names cs)
  ≡⟨ cong (xs ++_) $ mapMaybe-++ isInj₂ (map inj₁ as) _ ⟩
    xs ++ mapMaybe isInj₂ (map inj₁ as) ++ ids cs
  ≡⟨ cong (λ ◆ → xs ++ ◆ ++ _) $ mapMaybeIsInj₂∘mapInj₁ as ⟩
    xs ++ [] ++ ids cs
  ≡⟨ cong (xs ++_) $ sym $ L.++-identityˡ _ ⟩
    xs ++ ids cs
  ∎ where open ≡-Reasoning

data TxContract : Set
TxContracts  = List TxContract
TxVContracts = List (Value × TxContracts)

data TxContract where
  put_&reveal_if_⇒_ :
    (Σ Ids (_↦ TxInput′)) → Secrets → Predicate → TxContracts → TxContract
  withdraw : Participant → TxContract
  split : TxVContracts → TxContract
  _⇒_ : Participant → TxContract → TxContract
  after_⇒_ : Time → TxContract → TxContract

mutual
  reifyᶜ : TxContract → Contractᶜ
  reifyᶜ (put (xs , txoutXS) &reveal as if p ⇒ cs) =
    put (codom txoutXS) &reveal as if p ⇒ reifyᶜˢ cs
  reifyᶜ (withdraw p) =
    withdraw p
  reifyᶜ (split vcs) =
    split (reifyᵛᶜˢ vcs)
  reifyᶜ (p ⇒ c) =
    p ⇒ reifyᶜ c
  reifyᶜ (after t ⇒ c) =
    after t ⇒ reifyᶜ c

  reifyᶜˢ : TxContracts → Contractsᶜ
  reifyᶜˢ []       = []
  reifyᶜˢ (c ∷ cs) = reifyᶜ c ∷ reifyᶜˢ cs

  reifyᵛᶜˢ : TxVContracts → VContractsᶜ
  reifyᵛᶜˢ []               = []
  reifyᵛᶜˢ ((v , cs) ∷ vcs) = (v , reifyᶜˢ cs) ∷ reifyᵛᶜˢ vcs

instance
  Contract▷TxContract : Σ Contract Txout ▷ TxContract
  Contract▷TxContract .view = uncurry go
    module ∣Contract▷TxContract∣ where mutual
      go : (c : Contract) → Txout c → TxContract
      go c txout with c
      ... | put xs &reveal as if p ⇒ cs =
        let txoutC , txoutCS = destruct≡-++/↦ (ids-put≡ p cs) txout
        in put (xs , txoutC) &reveal as if p ⇒ gos cs txoutCS
      ... | withdraw p =
        withdraw p
      ... | split vcs =
        split (goss vcs txout)
      ... | p ⇒ c =
        p ⇒ go c (txout ∘ ∈-++⁺ʳ _)
      ... | after t ⇒ c =
        after t ⇒ go c txout

      gos : (cs : Contracts) → Txout cs → TxContracts
      gos []       _     = []
      gos cs₀@(c ∷ cs) txout =
        let
          n≡ : ids cs₀ ≡ ids c ++ ids cs
          n≡ = mapMaybe-++ isInj₂ (names c) (names cs)

          txoutC , txoutCS = destruct≡-++/↦ n≡ txout
        in
          go c txoutC ∷ gos cs txoutCS

      goss : (vcs : VContracts) → Txout vcs → TxVContracts
      goss [] _ = []
      goss vcs₀@((v , cs) ∷ vcs) txout =
        let
          n≡ : ids vcs₀ ≡ ids cs ++ ids vcs
          n≡ = mapMaybe-++ isInj₂ (names cs) (names vcs)

          txoutCS , txoutVCS = destruct≡-++/↦ n≡ txout
        in
          (v , gos cs txoutCS) ∷ goss vcs txoutVCS
  Contract▷TxContract .unview = go
    module ∣Contract▷TxContract∣˘ where mutual
      go : TxContract → ∃ λ (c : Contract) → Txout c
      go = λ where
        (put (xs , txoutXS) &reveal as if p ⇒ cs) →
          let cs′ , txoutCS = gos cs
          in (put xs &reveal as if p ⇒ cs′)
           , cong-↦ (txoutXS ++/↦ txoutCS) (ids-put≡ p cs′)
        (withdraw p) →
          withdraw p , λ ()
        (split vcs) →
          let vcs′ , txout = goss vcs
          in split vcs′ , txout
        (p ⇒ c) →
          let c′ , txout = go c
          in (p ⇒ c′) , txout
        (after t ⇒ c) →
          let c′ , txout = go c
          in (after t ⇒ c′) , txout

      gos : TxContracts → ∃ λ (cs : Contracts) → Txout cs
      gos [] = ([] , λ ())
      gos (c ∷ cs) =
        let c′  , txoutC  = go c
            cs′ , txoutCS = gos cs
            txout = cong-↦ (txoutC ++/↦ txoutCS)
                  $ mapMaybe-++ isInj₂ (names c′) (names cs′)
        in (c′ ∷ cs′) , txout

      goss : TxVContracts → ∃ λ (vcs : VContracts) → Txout vcs
      goss [] = ([] , λ ())
      goss ((v , cs) ∷ vcs) =
        let cs′  , txoutCS  = gos cs
            vcs′ , txoutVCS = goss vcs
            txout = cong-↦ (txoutCS ++/↦ txoutVCS)
                  $ mapMaybe-++ isInj₂ (names cs′) (names vcs′)
        in ((v , cs′) ∷ vcs′) , txout
  Contract▷TxContract .unview∘view = TODO
  Contract▷TxContract .view∘unview = TODO

  Contracts▷TxContracts : Σ Contracts Txout ▷ TxContracts
  Contracts▷TxContracts .view = uncurry ∣Contract▷TxContract∣.gos
  Contracts▷TxContracts .unview = ∣Contract▷TxContract∣˘.gos
  Contracts▷TxContracts .unview∘view = TODO
  Contracts▷TxContracts .view∘unview = TODO

  VContracts▷TxVContracts : Σ VContracts Txout ▷ TxVContracts
  VContracts▷TxVContracts .view = uncurry ∣Contract▷TxContract∣.goss
  VContracts▷TxVContracts .unview = ∣Contract▷TxContract∣˘.goss
  VContracts▷TxVContracts .unview∘view = TODO
  VContracts▷TxVContracts .view∘unview = TODO

data TxPrecondition : Set where
  _:?_at_ : Participant → Value → Id × TxInput′ → TxPrecondition
  _:!_at_ : Participant → Value → Id × TxInput′ → TxPrecondition
  _:secret_ : Participant → Secret → TxPrecondition
  _∣∣_ : TxPrecondition → TxPrecondition → TxPrecondition

reifyᵖ : TxPrecondition → Preconditionᶜ
reifyᵖ = λ where
  (p :? v at (x , o)) → p :? v at o
  (p :! v at (x , o)) → p :! v at o
  (p :secret s)       → p :secret s
  (p ∣∣ q)            → reifyᵖ p ∣∣ reifyᵖ q

instance
  Precondition▷TxPrecondition : Σ Precondition Txout ▷ TxPrecondition
  Precondition▷TxPrecondition .view = uncurry go
    where
      go : (p : Precondition) → Txout p → TxPrecondition
      go p txout with p
      ... | P :? v at x = P :? v at (x , txout (here refl))
      ... | P :! v at x = P :! v at (x , txout (here refl))
      ... | P :secret s = P :secret s
      ... | p ∣∣ q rewrite mapMaybe-++ isInj₂ (names p) (names q)
          = go p (txout ∘ ∈-++⁺ˡ) ∣∣ go q (txout ∘ ∈-++⁺ʳ _)
  Precondition▷TxPrecondition .unview = go
    where
      go : TxPrecondition → Σ Precondition Txout
      go (P :? v at (x , o)) = (P :? v at x) , (λ where (here refl) → o)
      go (P :! v at (x , o)) = (P :! v at x) , (λ where (here refl) → o)
      go (P :secret s)       = (P :secret s) , λ ()
      go (p ∣∣ q) =
        let p′ , txoutP = go p
            q′ , txoutQ = go q
            ids≡ = mapMaybe-++ isInj₂ (names p′) (names q′)
        in (p′ ∣∣ q′) , cong-↦ (txoutP ++/↦ txoutQ) ids≡
  Precondition▷TxPrecondition .unview∘view = TODO
  Precondition▷TxPrecondition .view∘unview = TODO

record TxAdvertisement : Set where
  constructor ⟨_⟩_
  field
    G : TxPrecondition
    C : TxContracts

reifyᵃᵈ : TxAdvertisement → Advertisementᶜ
reifyᵃᵈ (⟨ G ⟩ C) = ⟨ reifyᵖ G ⟩ reifyᶜˢ C

instance
  Ad▷TxAd : (∃ λ (ad : Ad) → Txout ad × Txout (ad .C)) ▷ TxAdvertisement
  Ad▷TxAd .view ((⟨ G ⟩ C) , txoutG , txoutC) =
    ⟨ view (G , λ {_} → txoutG) ⟩ view (C , λ {_} → txoutC)
  Ad▷TxAd .unview (⟨ G ⟩ C) =
    let G′ , txoutG = unview G
        C′ , txoutC = unview C
    in  (⟨ G′ ⟩ C′) , txoutG , txoutC
  Ad▷TxAd .unview∘view = TODO
  Ad▷TxAd .view∘unview = TODO

reify : (∃ λ (ad : Ad) → Txout ad × Txout (ad .C)) → Advertisementᶜ
reify = reifyᵃᵈ ∘ view

{-
mutual
  abstractᶜ : Contractᶜ → TxContract
  abstractᶜ _ = TODO
  -- open import Prelude.Show
  -- abstractᶜ (put vs &reveal as if p ⇒ cs) =
  --   put (dummyIds , txout) &reveal as if p ⇒ abstractᶜˢ cs
  --   where
  --     dummyIds : Ids
  --     dummyIds = map (λ n → "x_" ◇ show n) $ upTo (length vs)

  --     txout : dummyIds ↦ TxInput′
  --     txout x∈ = {!!} -- vs ‼ L.Any.index {!L.Any.map ? x∈!}
  -- abstractᶜ (withdraw p) =
  --   withdraw p
  -- abstractᶜ (split vcs) =
  --   split (abstractᵛᶜˢ vcs)
  -- abstractᶜ (p ⇒ c) =
  --   p ⇒ abstractᶜ c
  -- abstractᶜ (after t ⇒ c) =
  --   after t ⇒ abstractᶜ c

  abstractᶜˢ : Contractsᶜ → TxContracts
  abstractᶜˢ []       = []
  abstractᶜˢ (c ∷ cs) = abstractᶜ c ∷ abstractᶜˢ cs

  abstractᵛᶜˢ : VContractsᶜ → TxVContracts
  abstractᵛᶜˢ []               = []
  abstractᵛᶜˢ ((v , cs) ∷ vcs) = (v , abstractᶜˢ cs) ∷ abstractᵛᶜˢ vcs
-}

-- instance
  -- Serializable-TxContract : Serializable TxContract
  -- Serializable-TxContract .encode tc = encode (reifyᶜ tc)
  -- Serializable-TxContract .encode-injective = TODO
  -- Serializable-TxContract .decode = fmap abstractᶜ ∘ decode
  -- Serializable-TxContract .encode-decode m x .proj₁ = TODO
  -- Serializable-TxContract .encode-decode m x .proj₂ = TODO

  -- Serializable-Contract : Serializable (∃ λ (c : Contract) → Txout c)
  -- Serializable-Contract .encode (c , txout) = encode (mkTxContract c txout)
  -- Serializable-Contract .encode-injective = TODO
  -- Serializable-Contract .decode = {!!} -- fmap {!!} ∘ decode -- fmap abstractᶜ ∘ decode
  -- Serializable-Contract .encode-decode m x .proj₁ = TODO
  -- Serializable-Contract .encode-decode m x .proj₂ = TODO

-- ** De-bruijn contracts (indices instead of identifiers)
module _ (n : ℕ) where
  Id′  = Fin n
  Ids′ = List Id′

  data Contract′ : Set
  Contracts′  = List Contract′
  VContracts′ = List (Value × Contracts′)

  data Contract′ where
    put_&reveal_if_⇒_ : Ids′ → Secrets → Predicate → Contracts′ → Contract′
    withdraw : Participant → Contract′
    split : VContracts′ → Contract′
    _⇒_ : Participant → Contract′ → Contract′
    after_⇒_ : Time → Contract′ → Contract′

  data Precondition′ : Set where
    _:?_at_ : Participant → Value → Id′ → Precondition′
    _:!_at_ : Participant → Value → Id′ → Precondition′
    _:secret_ : Participant → Secret → Precondition′
    _∣∣_ : Precondition′ → Precondition′ → Precondition′

  record Advertisement′ : Set where
    constructor ⟨_⟩_
    field
      G : Precondition′
      C : Contracts′

  infix  2 ⟨_⟩_

  infix  5 _:?_at_
  infix  5 _:!_at_
  infix  5 _:secret_
  infixl 2 _∣∣_

  infixr 9 _⇒_
  infix  8 put_&reveal_if_⇒_

rei′ : ∀ {n} → (Fin n → Id) → Contract′ n → Contract
rei′ {n} getId = go
  where mutual
    go : Contract′ n → Contract
    go = λ where
      (put xs &reveal as if p ⇒ cs) →
        put (getId <$> xs) &reveal as if p ⇒ gos cs
      (withdraw p) →
        withdraw p
      (split vcs) →
        split (goss vcs)
      (p ⇒ c) →
        p ⇒ go c
      (after t ⇒ c) →
        after t ⇒ go c

    gos : Contracts′ n → Contracts
    gos = λ where
      [] → []
      (c ∷ cs) → go c ∷ gos cs

    goss : VContracts′ n → VContracts
    goss = λ where
      [] → []
      ((v , cs) ∷ css) → (v , gos cs) ∷ goss css

-- abs′ : Contract → ∃ Contract′
-- abs′ = {!!}

{-
reifyᶜ : (c : Contract) → Txout c → Contractᶜ
reifyᶜˢ : (cs : Contracts) → Txout cs → Contractsᶜ
reifyᶜˢ []       _     = []
reifyᶜˢ (c ∷ cs) txout = reifyᶜ c (txout ∘′ mapMaybe-⊆ isInj₂ ∈-++⁺ˡ) ∷ reifyᶜˢ cs (txout ∘ mapMaybe-⊆ isInj₂ (∈-++⁺ʳ _))
reifyᵛᶜˢ : (vcs : VContracts) → Txout vcs → VContractsᶜ
reifyᵛᶜˢ []               _     = []
reifyᵛᶜˢ ((v , cs) ∷ vcs) txout = (v , reifyᶜˢ cs {!!}) ∷ reifyᵛᶜˢ vcs {!!}
reifyᶜ (put xs &reveal as if p ⇒ cs) txout =
  put (mapWith∈ xs {!!}) &reveal as if p ⇒ reifyᶜˢ cs {!!}
reifyᶜ (withdraw p) txout =
  withdraw p
reifyᶜ (split vcs) txout =
  split (reifyᵛᶜˢ vcs {!!})
reifyᶜ (p ⇒ c) txout =
  p ⇒ reifyᶜ c (txout ∘ L.Mem.∈-++⁺ʳ _)
reifyᶜ (after t ⇒ c) txout =
  after t ⇒ reifyᶜ c txout

-- abstractᶜ : Contractᶜ → Contract
-- abstractᶜ = {!!}
-}
