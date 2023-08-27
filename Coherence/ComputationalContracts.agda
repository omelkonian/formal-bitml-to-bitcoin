open import Prelude.Init hiding (T); open SetAsType
open ≡-Reasoning
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Lists.Dec
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Views
open import Prelude.InferenceRules

open import Bitcoin using (HashId; TxInput′)
open import Prelude.Serializable HashId
open import BitML.BasicTypes using (⋯)

module Coherence.ComputationalContracts (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML ⋯ hiding (A; B; begin_; _∎; _▷_; g′)
open import Compiler.Mappings ⋯

-- ** Computational contracts (transaction outputs instead of identifiers)
Idᶜ  = TxInput′
Idsᶜ = List Idᶜ

data Branchᶜ : Type
Contractᶜ  = List Branchᶜ
VContractsᶜ = List (Value × Contractᶜ)

data Branchᶜ where
  put_&reveal_if_⇒_ : Idsᶜ → Secrets → Predicate → Contractᶜ → Branchᶜ
  withdraw : Participant → Branchᶜ
  split : VContractsᶜ → Branchᶜ
  _∶_ : Participant → Branchᶜ → Branchᶜ
  after_∶_ : Time → Branchᶜ → Branchᶜ

data Preconditionᶜ : Type where
  _:?_at_ : Participant → Value → Idᶜ → Preconditionᶜ
  _:!_at_ : Participant → Value → Idᶜ → Preconditionᶜ
  _:secret_ : Participant → Secret → Preconditionᶜ
  _∣_ : Preconditionᶜ → Preconditionᶜ → Preconditionᶜ

record Advertisementᶜ : Type where
  constructor ⟨_⟩_
  field
    G : Preconditionᶜ
    C : Contractᶜ

infix  7 _:?_at_ _:!_at_ _:secret_
infixl 6 _∣_
infix  0 ⟨_⟩_

infixr 9 _∶_ after_∶_
infix  8 put_&reveal_if_⇒_

postulate instance
  Serializable-Branchᶜ : Serializable Branchᶜ
  Serializable-Preconditionᶜ : Serializable Preconditionᶜ
  Serializable-Advertisementᶜ : Serializable Advertisementᶜ

-- ** De-bruijn contracts (indices instead of identifiers)
module _ (n : ℕ) where
  Id′  = Fin n
  Ids′ = List Id′

  data Branch′ : Type
  Contract′  = List Branch′
  VContracts′ = List (Value × Contract′)

  data Branch′ where
    put_&reveal_if_⇒_ : Ids′ → Secrets → Predicate → Contract′ → Branch′
    withdraw : Participant → Branch′
    split : VContracts′ → Branch′
    _∶_ : Participant → Branch′ → Branch′
    after_∶_ : Time → Branch′ → Branch′

  data Precondition′ : Type where
    _:?_at_ : Participant → Value → Id′ → Precondition′
    _:!_at_ : Participant → Value → Id′ → Precondition′
    _:secret_ : Participant → Secret → Precondition′
    _∣_ : Precondition′ → Precondition′ → Precondition′

  record Advertisement′ : Type where
    constructor ⟨_⟩_
    field
      G : Precondition′
      C : Contract′

  infix  7 _:?_at_ _:!_at_ _:secret_
  infixl 6 _∣_
  infix  0 ⟨_⟩_

  infixr 9 _∶_ after_∶_
  infix  8 put_&reveal_if_⇒_

rei′ : ∀ {n} → (Fin n → Id) → Branch′ n → Branch
rei′ {n} getId = go
  where mutual
    go : Branch′ n → Branch
    go = λ where
      (put xs &reveal as if p ⇒ cs) →
        put (getId <$> xs) &reveal as if p ⇒ gos cs
      (withdraw p) →
        withdraw p
      (split vcs) →
        split (goss vcs)
      (p ∶ c) →
        p ∶ go c
      (after t ∶ c) →
        after t ∶ go c

    gos : Contract′ n → Contract
    gos = λ where
      [] → []
      (c ∷ cs) → go c ∷ gos cs

    goss : VContracts′ n → VContracts
    goss = λ where
      [] → []
      ((v , cs) ∷ css) → (v , gos cs) ∷ goss css

{- simply-typed version (using normal function space)
  module _ (txout : Id → Idᶜ) where
    rei : Branch → Branchᶜ
    reis : Contract → Contractᶜ
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
      (p ∶ c) →
        p ∶ rei c
      (after t ∶ c) →
        after t ∶ rei c

  module _ (txout⁻¹ : Idᶜ → Id) where
    abs : Branchᶜ → Branch
    abss : Contractᶜ → Contract
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
      (p ∶ c) →
        p ∶ abs c
      (after t ∶ c) →
        after t ∶ abs c
-}

data TxBranch : Type
TxContract  = List TxBranch
TxVContracts = List (Value × TxContract)

data TxBranch where
  put_&reveal_if_⇒_ :
    (Σ Ids (_↦ TxInput′)) → Secrets → Predicate → TxContract → TxBranch
  withdraw : Participant → TxBranch
  split : TxVContracts → TxBranch
  _∶_ : Participant → TxBranch → TxBranch
  after_∶_ : Time → TxBranch → TxBranch

mutual
  reifyᶜ : TxBranch → Branchᶜ
  reifyᶜ (put (xs , txoutXS) &reveal as if p ⇒ cs) =
    put (codom txoutXS) &reveal as if p ⇒ reifyᶜˢ cs
  reifyᶜ (withdraw p) =
    withdraw p
  reifyᶜ (split vcs) =
    split (reifyᵛᶜˢ vcs)
  reifyᶜ (p ∶ c) =
    p ∶ reifyᶜ c
  reifyᶜ (after t ∶ c) =
    after t ∶ reifyᶜ c

  reifyᶜˢ : TxContract → Contractᶜ
  reifyᶜˢ []       = []
  reifyᶜˢ (c ∷ cs) = reifyᶜ c ∷ reifyᶜˢ cs

  reifyᵛᶜˢ : TxVContracts → VContractsᶜ
  reifyᵛᶜˢ []               = []
  reifyᵛᶜˢ ((v , cs) ∷ vcs) = (v , reifyᶜˢ cs) ∷ reifyᵛᶜˢ vcs

open import Prelude.Setoid
private postulate TODO : ∀ {X : Type ℓ} → X -- omit proofs of view laws

instance
  Setoid-TxBranch : ISetoid TxBranch
  Setoid-TxBranch .relℓ = 0ℓ
  Setoid-TxBranch ._≈_ = go
    module ∣Setoid-TxBranch∣ where mutual
      go : Rel₀ TxBranch
      go (put (xs , f) &reveal as if p ⇒ cs) (put (xs′ , f′) &reveal as′ if p′ ⇒ cs′) =
        ∃ λ (xs≡ : xs ≡ xs′)
        → (f ≗⟨ ↭-reflexive $ sym xs≡ ⟩↦ f′)
        × (as ≡ as′)
        × (p ≡ p′)
        × gos cs cs′
      go (withdraw p)  (withdraw p′)   = p ≡ p′
      go (split vcs)   (split vcs′)    = goss vcs vcs′
      go (p ∶ c) (p′ ∶ c′) = (p ≡ p′) × go c c′
      go (after t ∶ c) (after t′ ∶ c′) = (t ≡ t′) × go c c′
      go _ _ = ⊥

      gos : Rel₀ TxContract
      gos [] [] = ⊤
      gos (c ∷ cs) (c′ ∷ cs′) = go c c′ × gos cs cs′
      gos _ _ = ⊥

      goss : Rel₀ TxVContracts
      goss [] [] = ⊤
      goss ((v , cs) ∷ vcs) ((v′ , cs′) ∷ vcs′) = (v ≡ v′) × gos cs cs′ × goss vcs vcs′
      goss _ _ = ⊥

  Setoid-TxContract : ISetoid TxContract
  Setoid-TxContract = λ where
    .relℓ → 0ℓ
    ._≈_  → ∣Setoid-TxBranch∣.gos

  Setoid-TxVContracts : ISetoid TxVContracts
  Setoid-TxVContracts = λ where
    .relℓ → 0ℓ
    ._≈_  → ∣Setoid-TxBranch∣.goss

  Branch▷TxBranch : Σ Branch Txout ▷ TxBranch
  Branch▷TxBranch .view = uncurry go
    module ∣Branch▷TxBranch∣ where mutual
      go : (c : Branch) → Txout c → TxBranch
      go c txout with c
      ... | put xs &reveal as if p ⇒ cs =
        let txoutXS , txoutCS = destruct≡-++/↦ (ids-put≡ p cs) txout
        in put (xs , txoutXS) &reveal as if p ⇒ gos cs txoutCS
      ... | withdraw p =
        withdraw p
      ... | split vcs =
        split (goss vcs txout)
      ... | p ∶ c =
        p ∶ go c (txout ∘ ∈-++⁺ʳ _)
      ... | after t ∶ c =
        after t ∶ go c txout

      gos : (cs : Contract) → Txout cs → TxContract
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
  Branch▷TxBranch .unview = go
    module ∣Branch▷TxBranch∣˘ where mutual
      go : TxBranch → ∃ λ (c : Branch) → Txout c
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
        (p ∶ c) →
          let c′ , txout = go c
          in (p ∶ c′) , txout
        (after t ∶ c) →
          let c′ , txout = go c
          in (after t ∶ c′) , txout

      gos : TxContract → ∃ λ (cs : Contract) → Txout cs
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
  Branch▷TxBranch .unview∘view = TODO
  Branch▷TxBranch .view∘unview = TODO

  Contract▷TxContract : Σ Contract Txout ▷ TxContract
  Contract▷TxContract .view = uncurry ∣Branch▷TxBranch∣.gos
  Contract▷TxContract .unview = ∣Branch▷TxBranch∣˘.gos
  Contract▷TxContract .unview∘view = TODO
  Contract▷TxContract .view∘unview = TODO

  VContracts▷TxVContracts : Σ VContracts Txout ▷ TxVContracts
  VContracts▷TxVContracts .view = uncurry ∣Branch▷TxBranch∣.goss
  VContracts▷TxVContracts .unview = ∣Branch▷TxBranch∣˘.goss
  VContracts▷TxVContracts .unview∘view = TODO
  VContracts▷TxVContracts .view∘unview = TODO

data TxPrecondition : Type where
  _:?_at_ : Participant → Value → Id × TxInput′ → TxPrecondition
  _:!_at_ : Participant → Value → Id × TxInput′ → TxPrecondition
  _:secret_ : Participant → Secret → TxPrecondition
  _∣_ : TxPrecondition → TxPrecondition → TxPrecondition

reifyᵖ : TxPrecondition → Preconditionᶜ
reifyᵖ = λ where
  (p :? v at (x , o)) → p :? v at o
  (p :! v at (x , o)) → p :! v at o
  (p :secret s)       → p :secret s
  (p ∣ q)            → reifyᵖ p ∣ reifyᵖ q

instance
  Precondition▷TxPrecondition : Σ Precondition Txout ▷ TxPrecondition
  Precondition▷TxPrecondition .view = uncurry go
    where
      go : (p : Precondition) → Txout p → TxPrecondition
      go p txout with p
      ... | P :? v at x = P :? v at (x , txout (here refl))
      ... | P :! v at x = P :! v at (x , txout (here refl))
      ... | P :secret s = P :secret s
      ... | p ∣ q =
        let
          ids≡ = mapMaybe-++ isInj₂ (names p) (names q)
          txoutP , txoutQ = destruct≡-++/↦ ids≡ txout
        in
          go p txoutP ∣ go q txoutQ
  Precondition▷TxPrecondition .unview = go
    where
      go : TxPrecondition → Σ Precondition Txout
      go (P :? v at (x , o)) = (P :? v at x) , (λ where (here refl) → o)
      go (P :! v at (x , o)) = (P :! v at x) , (λ where (here refl) → o)
      go (P :secret s)       = (P :secret s) , λ ()
      go (p ∣ q) =
        let p′ , txoutP = go p
            q′ , txoutQ = go q
            ids≡ = mapMaybe-++ isInj₂ (names p′) (names q′)
        in (p′ ∣ q′) , cong-↦ (txoutP ++/↦ txoutQ) ids≡
  Precondition▷TxPrecondition .unview∘view = TODO
  Precondition▷TxPrecondition .view∘unview = TODO

record TxAd : Type where
  constructor ⟨_⟩_
  field
    G : TxPrecondition
    C : TxContract

reifyᵃᵈ : TxAd → Advertisementᶜ
reifyᵃᵈ (⟨ G ⟩ C) = ⟨ reifyᵖ G ⟩ reifyᶜˢ C

instance
  Setoid-TxAd : ISetoid TxAd
  Setoid-TxAd .relℓ = 0ℓ
  Setoid-TxAd ._≈_ (⟨ g ⟩ cs) (⟨ g′ ⟩ cs′) = (g ≡ g′) × (cs ≈ cs′)

  Ad▷TxAd : (∃ λ (ad : Ad) → Txout ad × Txout (ad .C)) ▷ TxAd
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

encodeAd : (ad : Ad) → Txout ad × Txout (ad .C) → HashId
encodeAd ad (txoutG , txoutC) = encode $ reify (ad , txoutG , txoutC)

open import Prelude.Lists.Collections

idsᶜ : ∀ {X : Type} ⦃ _ : X has Idᶜ ⦄ → (X → Idsᶜ)
idsᶜ = collect

instance
  HGᵗˣⁱ : Preconditionᶜ has TxInput′
  HGᵗˣⁱ .collect = λ where
    (_ :secret _) → []
    (_ :? _ at x) → [ x ]
    (_ :! _ at x) → [ x ]
    (p ∣ q) → collect p ++ collect q

  HCᵗˣⁱ : Branchᶜ has TxInput′
  HCᵗˣⁱ .collect = go
    module ∣HCᵗˣⁱ∣ where mutual
      go : Branchᶜ → Idsᶜ
      go = λ where
        (put xs &reveal _ if _ ⇒ cs) → xs ++ gos cs
        (withdraw _)                 → []
        (split vcs)                  → goss vcs
        (_ ∶ c′)                     → go c′
        (after _ ∶ c′)               → go c′

      gos : Contractᶜ → Idsᶜ
      gos [] = []
      gos (c ∷ cs) = go c ++ gos cs

      goss : VContractsᶜ → Idsᶜ
      goss [] = []
      goss ((v , cs) ∷ vcs) = gos cs ++ goss vcs

  HCSᵗˣⁱ : Contractᶜ has TxInput′
  HCSᵗˣⁱ .collect = ∣HCᵗˣⁱ∣.gos

  HVCSᵗˣⁱ : VContractsᶜ has TxInput′
  HVCSᵗˣⁱ .collect = ∣HCᵗˣⁱ∣.goss

  HAᵗˣⁱ : Advertisementᶜ has TxInput′
  HAᵗˣⁱ .collect (⟨ g ⟩ c) = collect g ++ collect c

Txout⁻¹ : ∀ {X : Type} → ⦃ X has Idᶜ ⦄ → Pred₀ X
Txout⁻¹ x = idsᶜ x ↦ Id

-- T0D0: move to Prelude.Lists.Mappings
destruct-++/↦-≡ : ∀ {A : Type} {P : A → Type} {xs ys : List A} {h h′ : xs ++ ys ↦′ P} →
  ∙ h ≗↦ h′
    ───────────────────────────────────────
    let f  , g  = destruct-++/↦ {ys = ys} h
        f′ , g′ = destruct-++/↦ {ys = ys} h′
    in (f ≗↦ f′) × (g ≗↦ g′)
destruct-++/↦-≡ eq = (λ _ → eq _) , (λ _ → eq _)

codom∘codom-↦ : ∀ {A B : Type} {xs : List A} (f : xs ↦ B) →
  codom (codom-↦ f) ≡ xs
codom∘codom-↦ {xs = []} _ = refl
codom∘codom-↦ {xs = x ∷ xs} f = cong (x ∷_) ( codom∘codom-↦ {xs = xs} (uncons-↦ f))

≗↦⇒codom≡ : ∀ {A B : Type} {xs : List A} {f f′ : xs ↦ B} →
  f ≗↦ f′
  ──────────────────
  codom f ≡ codom f′
≗↦⇒codom≡ {xs = []} _ = refl
≗↦⇒codom≡ {B = B} {xs = x ∷ xs} {f}{f′} eq
  rewrite eq (here refl)
  = cong (_ ∷_) $ ≗↦⇒codom≡ {xs = xs} (λ _ → eq _)

codom∘destruct∘codom-↦ˡ : ∀ {A B : Type} {xs : List A} {ys : List B}
  (f : xs ↦ B) (g : ys ↦ A) →
  codom (destruct-++/↦ {xs = codom f} (codom-↦ f ++/↦ g) .proj₁) ≡ xs
codom∘destruct∘codom-↦ˡ {xs = xs} f g =
  begin
    codom (destruct-++/↦ (codom-↦ f ++/↦ g) .proj₁)
  ≡˘⟨ ≗↦⇒codom≡ $ destruct-++/↦∘++/↦ (codom-↦ f) g .proj₁ ⟩
    codom (codom-↦ f)
  ≡⟨ codom∘codom-↦ f ⟩
    xs
  ∎

codom∘destruct∘codom-↦ʳ : ∀ {A B : Type} {ys : List A} {xs : List B}
  (f : xs ↦ A) (g : ys ↦ B) →
  codom (destruct-++/↦ {ys = codom g} (f ++/↦ codom-↦ g) .proj₂) ≡ ys
codom∘destruct∘codom-↦ʳ {ys = ys} f g =
  begin
    codom (destruct-++/↦ (f ++/↦ codom-↦ g) .proj₂)
  ≡˘⟨ ≗↦⇒codom≡ $ destruct-++/↦∘++/↦ f (codom-↦ g) .proj₂ ⟩
    codom (codom-↦ g)
  ≡⟨ codom∘codom-↦ g ⟩
    ys
  ∎

codom∘destruct≡∘codom-↦ˡ : ∀ {A B : Type} {xs : List A} {ys zs : List B}
  (f : xs ↦ B) (g : ys ↦ A)
  (eq : zs ≡ codom f ++ ys) →
  codom (destruct≡-++/↦ {xs = codom f} eq (cong-↦ (codom-↦ f ++/↦ g) eq) .proj₁) ≡ xs
codom∘destruct≡∘codom-↦ˡ f g refl = codom∘destruct∘codom-↦ˡ f g

codom∘destruct≡∘codom-↦ʳ : ∀ {A B : Type} {ys : List A} {xs zs : List B}
  (f : xs ↦ A) (g : ys ↦ B)
  (eq : zs ≡ xs ++ codom g) →
  codom (destruct≡-++/↦ {ys = codom g} eq (cong-↦ (f ++/↦ codom-↦ g) eq) .proj₂) ≡ ys
codom∘destruct≡∘codom-↦ʳ f g refl = codom∘destruct∘codom-↦ʳ f g

_∣/≡_ : ∀ {p p′ q q′} →
  ∙ p ≡ p′
  ∙ q ≡ q′
    ────────────────────────────────────
    (Precondition ∋ p ∣ q) ≡ (p′ ∣ q′)
refl ∣/≡ refl = refl

_∣/≡ᵗˣ_ : ∀ {p p′ q q′} →
  ∙ p ≡ p′
  ∙ q ≡ q′
    ──────────────────────────────────────
    (TxPrecondition ∋ p ∣ q) ≡ (p′ ∣ q′)
refl ∣/≡ᵗˣ refl = refl

_∣/≡ᶜ_ : ∀ {p p′ q q′} →
  ∙ p ≡ p′
  ∙ q ≡ q′
    ─────────────────────────────────────
    (Preconditionᶜ ∋ p ∣ q) ≡ (p′ ∣ q′)
refl ∣/≡ᶜ refl = refl

_∷/≡_ : ∀ {A : Type ℓ} {x x′ : A} {xs xs′ : List A} →
  ∙ x ≡ x′
  ∙ xs ≡ xs′
    ──────────────────────────────
    (List A ∋ x ∷ xs) ≡ (x′ ∷ xs′)
refl ∷/≡ refl = refl

_++/≡_ : ∀ {A : Type ℓ} {xs xs′ ys ys′ : List A} →
  ∙ xs ≡ xs′
  ∙ ys ≡ ys′
    ──────────────────────────────────
    (List A ∋ xs ++ ys) ≡ (xs′ ++ ys′)
refl ++/≡ refl = refl

⟨_⟩/≡_ : ∀ {g g′ c c′} →
  ∙ g ≡ g′
  ∙ c ≈ c′
    ─────────────────────────────
    (TxAd ∋ (⟨ g ⟩ c)) ≈
    (⟨ g′ ⟩ c′)
⟨_⟩/≡_ = _,_

put_⇒/≡_ : ∀ {xs xs′ cs cs′} {as p} →
  ∙ xs ≡ xs′
  ∙ cs ≡ cs′
    ──────────────────────────────
    (Branchᶜ ∋ put xs &reveal as if p ⇒ cs) ≡
    (put xs′ &reveal as if p ⇒ cs′)
put refl ⇒/≡ refl = refl
--

module ∣view≡∣ where
  goᵖ : ∀ (g : Precondition) {txout txout′ : Txout g} →
    txout ≗↦ txout′
    ──────────────────────────
    view (g , λ {_} → txout) ≡
    view (g , λ {_} → txout′)
  goᵖ (_ :? x₁ at _) eq rewrite eq (here refl) = refl
  goᵖ (_ :! x₁ at _) eq rewrite eq (here refl) = refl
  goᵖ (_ :secret _) _ = refl
  goᵖ (p ∣ q) {txout}{txout′} eq
    rewrite mapMaybe-++ isInj₂ (names p) (names q)
    = goᵖ p (λ _ → eq _) ∣/≡ᵗˣ goᵖ q (λ _ → eq _)

  mutual
    go : ∀ (c : Branch) {txout txout′ : Txout c} →
      txout ≗↦ txout′
      ──────────────────────────
      view (c , λ {_} → txout) ≈
      view (c , λ {_} → txout′)
    go (put xs &reveal as if p ⇒ cs) eq
      rewrite ids-put≡ {xs = xs}{as} p cs
      = let txoutXS≗ , txoutCS≗ = destruct-++/↦-≡ {xs = xs}{ys = ids cs} eq
        in refl , txoutXS≗ , refl , refl , gos cs txoutCS≗
    go (withdraw _)   _  = refl
    go (split vcs)    eq = goss vcs eq -- cong split $ goss vcs eq
    go (_ ∶ c′)       eq = refl , go c′ eq -- cong (_ ∶_) $ go c′ eq
    go (after _ ∶ c′) eq = refl , go c′ eq -- cong (after _ ∶_) $ go c′ eq

    gos : ∀ (cs : Contract) {txout txout′ : Txout cs} →
      txout ≗↦ txout′
      ───────────────────────────
      view (cs , λ {_} → txout) ≈
      view (cs , λ {_} → txout′)
    gos [] _ = tt
    gos (c ∷ cs) eq
      rewrite mapMaybe-++ isInj₂ (names c) (names cs)
      = let txoutC≗ , txoutCS≗ = destruct-++/↦-≡ eq
        in go c txoutC≗ , gos cs txoutCS≗

    goss : ∀ (vcs : VContracts) {txout txout′ : Txout vcs} →
      txout ≗↦ txout′
      ────────────────────────────
      view (vcs , λ {_} → txout) ≈
      view (vcs , λ {_} → txout′)
    goss [] _ = tt
    goss ((v , cs) ∷ vcs) eq
      rewrite mapMaybe-++ isInj₂ (names cs) (names vcs)
      = let txoutCS≗ , txoutVCS≗ = destruct-++/↦-≡ eq
        in refl , gos cs txoutCS≗ , goss vcs txoutVCS≗

view≡ : ∀ {ad} {txoutG txoutG′ : Txout ad} {txoutC txoutC′ : Txout (ad .C)} →
  ∙ txoutG ≗↦ txoutG′
  ∙ txoutC ≗↦ txoutC′
    ────────────────────────────────────────────────
    view (ad , (λ {_} → txoutG)  , λ {_} → txoutC) ≈
    view (ad , (λ {_} → txoutG′) , λ {_} → txoutC′)
view≡ {⟨ g ⟩ c} txoutG≗ txoutC≗ = ⟨ goᵖ g txoutG≗ ⟩/≡ gos c txoutC≗
  where open ∣view≡∣

module ∣reify≡∣ where mutual
  go : ∀ (c c′ : TxBranch) →
    c ≈ c′
    ────────────────────
    reifyᶜ c ≡ reifyᶜ c′
  go (put _ &reveal _ if _ ⇒ _) (put _ &reveal _ if _ ⇒ _)
      (refl , xs≈ , refl , refl , cs≈)
      rewrite gos _ _ cs≈ | ≗↦⇒codom≡ xs≈ = refl
  go (withdraw _) (withdraw _) refl = refl
  go (split _) (split _) vcs≈ rewrite goss _ _ vcs≈ = refl
  go (_ ∶ c) (_ ∶ c′) (refl , c≈) rewrite go c c′ c≈ = refl
  go (after _ ∶ c) (after _ ∶ c′) (refl , c≈) rewrite go c c′ c≈ = refl

  gos : ∀ (cs cs′ : TxContract) →
    cs ≈ cs′
    ────────────────────────
    reifyᶜˢ cs ≡ reifyᶜˢ cs′
  gos [] [] tt = refl
  gos (c ∷ cs) (c′ ∷ cs′) (c≈ , cs≈) = go c c′ c≈ ∷/≡ gos cs cs′ cs≈

  goss : ∀ (vcs vcs′ : TxVContracts) →
    vcs ≈ vcs′
    ────────────────────────────
    reifyᵛᶜˢ vcs ≡ reifyᵛᶜˢ vcs′
  goss [] [] tt = refl
  goss ((v , cs) ∷ vcs) ((v , cs′) ∷ vcs′) (refl , cs≈ , vcs≈) =
    cong (v ,_) (gos cs cs′ cs≈) ∷/≡ goss vcs vcs′ vcs≈

reify≡ : ∀ {ad ad′ : TxAd} →
  ad ≈ ad′
  ────────────────────────────────────────────────
  reifyᵃᵈ ad ≡ reifyᵃᵈ ad′
reify≡ (refl , cs≈) rewrite ∣reify≡∣.gos _ _ cs≈ = refl

abstractᶜ : (adᶜ : Advertisementᶜ) → Txout⁻¹ adᶜ
  → ∃ λ (ad : Ad) → Txout ad × Txout (ad .C)
abstractᶜ (⟨ g ⟩ c) txout⁻¹ =
  let txoutG , txoutC = destruct-++/↦ txout⁻¹
      g , txoutG = goᵖ g txoutG
      c , txoutC = gos c txoutC
  in (⟨ g ⟩ c) , txoutG , txoutC
  module ∣abstractᶜ∣ where
    mutual
      go : (c : Branchᶜ) → Txout⁻¹ c → ∃ λ (c : Branch) → Txout c
      go c txout⁻¹ with c
      ... | put xs &reveal as if p ⇒ cs =
        let txoutXS , txoutCS = destruct-++/↦ txout⁻¹
            cs , txoutCS = gos cs txoutCS
            ids≡ = ids-put≡ p cs
        in put codom txoutXS &reveal as if p ⇒ cs
         , cong-↦ (codom-↦ txoutXS ++/↦ txoutCS) ids≡
      ... | withdraw p =
        withdraw p , λ ()
      ... | split vcs =
        let vcs , txout = goss vcs txout⁻¹
        in split vcs , txout
      ... | p ∶ c =
        let c , txout = go c txout⁻¹
        in (p ∶ c) , txout
      ... | after t ∶ c =
        let c , txout = go c txout⁻¹
        in (after t ∶ c) , txout

      gos : (cs : Contractᶜ) → Txout⁻¹ cs → ∃ λ (cs : Contract) → Txout cs
      gos [] _ = [] , λ ()
      gos (c ∷ cs) txout⁻¹ =
        let c , txoutC = go c (txout⁻¹ ∘ ∈-++⁺ˡ)
            cs , txoutCS = gos cs (txout⁻¹ ∘ ∈-++⁺ʳ _)
            ids≡ = mapMaybe-++ isInj₂ (names c) (names cs)
        in (c ∷ cs) , cong-↦ (txoutC ++/↦ txoutCS) ids≡

      goss : (vcs : VContractsᶜ) → Txout⁻¹ vcs → ∃ λ (vcs : VContracts) → Txout vcs
      goss [] _ = [] , λ ()
      goss ((v , cs) ∷ vcs) txout⁻¹ =
        let cs , txoutCS = gos cs (txout⁻¹ ∘ ∈-++⁺ˡ)
            vcs , txoutVCS = goss vcs (txout⁻¹ ∘ ∈-++⁺ʳ _)
            ids≡ = mapMaybe-++ isInj₂ (names cs) (names vcs)
        in ((v , cs) ∷ vcs) , cong-↦ (txoutCS ++/↦ txoutVCS) ids≡

    pattern 𝟘 = here refl

    goᵖ : (g : Preconditionᶜ) → Txout⁻¹ g → ∃ λ (g : Precondition) → Txout g
    goᵖ g txout⁻¹ with g
    ... | A :secret s = A :secret s , λ ()
    ... | A :? v at i = A :? v at txout⁻¹ 𝟘 , λ where 𝟘 → i
    ... | A :! v at i = A :! v at txout⁻¹ 𝟘 , λ where 𝟘 → i
    ... | p ∣ q =
      let p , txoutP = goᵖ p (txout⁻¹ ∘ ∈-++⁺ˡ)
          q , txoutQ = goᵖ q (txout⁻¹ ∘ ∈-++⁺ʳ _)
          ids≡ = mapMaybe-++ isInj₂ (names p) (names q)
      in (p ∣ q) , cong-↦ (txoutP ++/↦ txoutQ) ids≡

reify∘abstract : ∀ adᶜ (txout⁻¹ : Txout⁻¹ adᶜ)
  → reify (abstractᶜ adᶜ txout⁻¹) ≡ adᶜ
reify∘abstract (⟨ g ⟩ cs) txout⁻¹ =
  let g′  = reifyᵖ  $ view $ goᵖ g  (txout⁻¹ ∘ ∈-++⁺ˡ)
      cs′ = reifyᶜˢ $ view $ gos cs (txout⁻¹ ∘ ∈-++⁺ʳ _)
  in begin
    (⟨ g′ ⟩ cs′)
  ≡⟨ cong (λ ◆ → ⟨ ◆ ⟩ cs′) $ Goᵖ g _ ⟩
    (⟨ g ⟩ cs′)
  ≡⟨ cong (λ ◆ → ⟨ _ ⟩ ◆) $ Gos cs _ ⟩
    (⟨ g ⟩ cs)
  ∎
  where
    open ∣abstractᶜ∣ g cs txout⁻¹
    open ≡-Reasoning

    Goᵖ : ∀ (g : Preconditionᶜ) (txout⁻¹ : Txout⁻¹ g) →
      reifyᵖ (view $ goᵖ g txout⁻¹) ≡ g
    Goᵖ g txout⁻¹ with g
    ... | _ :secret _ = refl
    ... | _ :? _ at _ = refl
    ... | _ :! _ at _ = refl
    ... | pᶜ ∣ qᶜ =
      let
        p≡ = Goᵖ pᶜ (txout⁻¹ ∘ ∈-++⁺ˡ)
        p , txoutP = goᵖ pᶜ (txout⁻¹ ∘ ∈-++⁺ˡ)
        q≡ = Goᵖ qᶜ (txout⁻¹ ∘ ∈-++⁺ʳ _)
        q , txoutQ = goᵖ qᶜ (txout⁻¹ ∘ ∈-++⁺ʳ _)
        ids≡ = mapMaybe-++ isInj₂ (names p) (names q)
        txoutP≗ , txoutQ≗ = destruct≡-++/↦∘cong-↦ txoutP txoutQ ids≡
      in
        trans (cong reifyᵖ $ sym (∣view≡∣.goᵖ p txoutP≗)) p≡
        ∣/≡ᶜ
        trans (cong reifyᵖ $ sym (∣view≡∣.goᵖ q txoutQ≗)) q≡

    mutual
      Go : (c : Branchᶜ) (txout⁻¹ : Txout⁻¹ c) →
        reifyᶜ (view $ go c txout⁻¹) ≡ c
      Go c txout⁻¹ with c
      ... | put xs &reveal as if p ⇒ cs =
        let txoutXS , txoutCS = destruct-++/↦ txout⁻¹
            cs≡ = Gos cs txoutCS
            cs , txoutCS = gos cs txoutCS
            ids≡ = ids-put≡ p cs
            txoutXS≗ , txoutCS≗ = destruct≡-++/↦∘cong-↦ (codom-↦ txoutXS) txoutCS ids≡
        in
        put
        codom∘destruct≡∘codom-↦ˡ txoutXS txoutCS ids≡
        ⇒/≡
        trans (sym $ ∣reify≡∣.gos _ _ $ ∣view≡∣.gos _ txoutCS≗) cs≡
      ... | withdraw _ = refl
      ... | split vcs =
        let vcs≡ = Goss vcs txout⁻¹
            vcs , txout = goss vcs txout⁻¹
        in cong split vcs≡
      ... | p ∶ c =
        let c≡ = Go c txout⁻¹
            c , txout = go c txout⁻¹
        in cong (p ∶_) c≡
      ... | after t ∶ c =
        let c≡ = Go c txout⁻¹
            c , txout = go c txout⁻¹
        in cong (after t ∶_) c≡

      Gos : (cs : Contractᶜ) (txout⁻¹ : Txout⁻¹ cs) →
        reifyᶜˢ (view $ gos cs txout⁻¹) ≡ cs
      Gos [] _ = refl
      Gos (c ∷ cs) txout⁻¹
        =
        let c≡ = Go c (txout⁻¹ ∘ ∈-++⁺ˡ)
            c′ , txoutC   = go c (txout⁻¹ ∘ ∈-++⁺ˡ)
            cs≡ = Gos cs (txout⁻¹ ∘ ∈-++⁺ʳ _)
            cs′ , txoutCS = gos cs (txout⁻¹ ∘ ∈-++⁺ʳ _)
            ids≡ = mapMaybe-++ isInj₂ (names c′) (names cs′)
            txoutC≗ , txoutCS≗ = destruct≡-++/↦∘cong-↦ txoutC txoutCS ids≡
        in
        trans (sym $ ∣reify≡∣.go _ _ $ ∣view≡∣.go c′ txoutC≗) c≡
        ∷/≡
        trans (sym $ ∣reify≡∣.gos _ _ $ ∣view≡∣.gos _ txoutCS≗) cs≡
      Goss : (vcs : VContractsᶜ) (txout⁻¹ : Txout⁻¹ vcs) →
        reifyᵛᶜˢ (view $ goss vcs txout⁻¹) ≡ vcs
      Goss [] _ = refl
      Goss ((v , cs) ∷ vcs) txout⁻¹
        =
        let cs≡ = Gos cs (txout⁻¹ ∘ ∈-++⁺ˡ)
            cs′ , txoutCS = gos cs (txout⁻¹ ∘ ∈-++⁺ˡ)
            vcs≡ = Goss vcs (txout⁻¹ ∘ ∈-++⁺ʳ _)
            vcs′ , txoutVCS = goss vcs (txout⁻¹ ∘ ∈-++⁺ʳ _)
            ids≡ = mapMaybe-++ isInj₂ (names cs′) (names vcs′)
            txoutCS≗ , txoutVCS≗ = destruct≡-++/↦∘cong-↦ txoutCS txoutVCS ids≡
        in
        cong (v ,_) (trans (sym $ ∣reify≡∣.gos _ _ $ ∣view≡∣.gos _ txoutCS≗) cs≡)
        ∷/≡
        trans (sym $ ∣reify≡∣.goss _ _ $ ∣view≡∣.goss _ txoutVCS≗) vcs≡

decodeAd : HashId
         → Σ Ids (_↦ TxInput′)
         → Maybe $ ∃ λ (ad : Ad) → Txout ad × Txout (ad .C)
decodeAd m (xs , txout)
  with decode {A = Advertisementᶜ} m
... | nothing  = nothing
... | just adᶜ
  with idsᶜ adᶜ ⊆? codom txout
... | no  ins⊈ = nothing
... | yes ins⊆ = just $ abstractᶜ adᶜ (codom-↦ txout ∘ ins⊆)

-- abstract∘reify : ∀ ad (txoutG : Txout ad) (txoutC : Txout (ad .C))
--   → abstractᶜ (reify (ad , txoutG , txoutC)) {!!}
--   ≡ (ad , txoutG , txoutC)
-- abstract∘reify ad txoutG txoutC = {!!}
