----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------

open import Data.Fin as Fin using (raise; inject+; toℕ)


open import Data.Nat.Properties using (≤-refl; <-trans; n<1+n)
open import Data.List.Membership.Setoid.Properties         using (length-mapWith∈)
open import Data.List.Relation.Unary.Any                   using (index)

open import Data.List.Relation.Unary.All                   using (lookup)

open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)

open import Relation.Binary.PropositionalEquality using (setoid)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecLists
open L.Mem
-- open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Functor
open import Prelude.Validity

-- Bitcoin
open import Bitcoin hiding (Value; Time)
-- open import Bitcoin.Crypto
-- open import Bitcoin.Script
-- open import Bitcoin.Tx

module SecureCompilation.Compiler

  -- BitML parameters
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  -- Compilation parameters
  (η : ℕ) -- public security nonce η, ensures adversaries cannot guess
  where

-- BitML

-- open import BitML
--   hiding (Value; C; `_; _`+_; _`-_; ∣_∣; `true; `false)
-- open Induction

open import BitML.BasicTypes
open import BitML.Predicate
  using (Predicate; Arith)
open import BitML.Contracts Participant Honest
  hiding (C)
open Induction

open import SymbolicModel.Collections Participant Honest
open import SymbolicModel.Mappings Participant Honest

-- single-output transactions
Tx¹ : ℕ → Set
Tx¹ i = Tx i 1
∃Tx¹ = ∃ Tx¹

-- contract-dependent outputs
outputLen : Contract → ℕ
outputLen (split vcs) = length vcs
outputLen _           = 1

Txᶜ : ℕ → Contract → Set
Txᶜ i c = Tx i (outputLen c)

∃Txᶜ : Contract → Set
∃Txᶜ c = ∃ λ i → Txᶜ i c

∃∃Txᶜ = ∃ ∃Txᶜ


bitml-compiler : let ⟨ g ⟩ ds = ad in
    -- the input contract & precondition (only compile valid advertisements)
    Valid ad
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (sechash : Sechash g)
    -- txout: maps deposits in G to *pre-existing* transactions with the corresponding value
  → (txout : Txout g)
    -- Exchanged keypairs K(A) and K(D,A)
  → (K : 𝕂 g)
  → (K² : 𝕂²′ ad)
    -- a set of transactions to be submitted
  → ∃Tx¹ × (subtermsᶜ⁺ ds ↦′ ∃Txᶜ)
bitml-compiler {ad = ⟨ G₀ ⟩ C₀} (record {names-⊆ = names⊆; names-put = putComponents⊆; participants-⊆ = part⊆})
  sechash₀ txout₀ K K²
  = Tᵢₙᵢₜ , (≺-rec _ go) CS₀ record
      { T,o     = Tᵢₙᵢₜ♯ at 0
      ; curV    = V₀
      ; P       = partG , ⊆-refl
      ; curT    = 0
      ; p⊆      = nub-⊆⁺ ∘ p⊆₀
      ; s⊆      = id
      ; ∃s      = tt
      ; sechash = sechash₀ ∘ mapMaybe-⊆ isInj₁ names⊆
      ; txout   = txout₀ ∘ mapMaybe-⊆ isInj₂ names⊆
      ; part    = part₀ ∘ mapMaybe-⊆ isInj₂ names⊆
      ; val     = val₀ ∘ mapMaybe-⊆ isInj₂ names⊆ }
  where
    CS₀   = CS C₀
    partG = nub-participants G₀
    ς     = length partG
    V₀    = sum (map (proj₁ ∘ proj₂) (persistentDeposits G₀))

    p⊆₀ : participants C₀ ⊆ participants G₀
    p⊆₀ = persistentParticipants⊆ {G₀} ∘ part⊆ ∘ ∈-++⁺ʳ (participants G₀)

    -- part: maps deposit names in G to the corresponding participant
    part₀ : namesʳ G₀ ↦ ∃ (_∈ partG)
    part₀ = -,_ ∘ ∈-nub⁺ ∘ proj₂ ∘ getDeposit {g = G₀}

    private variable X : Set

    Part : ⦃ _ : X has Name ⦄ → Pred₀ X
    Part x = namesʳ x ↦ ∃ (_∈ partG)

    -- val: maps deposit names in G to the value contained in the deposit
    val₀ : namesʳ G₀ ↦ Value
    val₀ = proj₁ ∘ proj₂ ∘ proj₁ ∘ getDeposit {g = G₀}

    Val : ⦃ _ : X has Name ⦄ → Pred₀ X
    Val x = namesʳ x ↦ Value

    -- Bout
    Bout : subterms′ CS₀ ↦ (∃[ ctx ] Script ctx `Bool)
    Bout {D} D∈ with removeTopDecorations D | inspect removeTopDecorations D
    ... | put zs &reveal as if p ⇒ _ | ≡[ eq ]
        = Ctx (ς + m) , ( versig (mapWith∈ partG (K² D∈)) (map (inject+ m) (allFin ς))
                     `∧ Bᵖʳ p p⊆as
                     `∧ ⋀ (mapEnumWith∈ as (λ i a a∈ →
                             let bi = var (raise ς i)
                             in (hash bi `= ` (sechash₀ (as⊆ a∈))) `∧ (` (+ η) `< Script.∣ bi ∣)))
                        )
      where
        m : ℕ
        m = length as

        p⊆ : putComponents D ⊆ putComponents C₀
        p⊆ = subterms′-putComponents⊆ᶜˢ {ds = C₀} D∈

        n⊆ : names D ⊆ names C₀
        n⊆ = subterms′-names⊆ᶜˢ {d = D} {ds = C₀} D∈

        put∈ : (zs , as , p) ∈ putComponents D
        put∈ rewrite remove-putComponents {D} | eq = here refl

        p⊆as : secrets p ⊆ as
        p⊆as = proj₂ (lookup putComponents⊆ (p⊆ put∈))

        as⊆ : as ⊆ namesˡ G₀
        as⊆ = (λ x → ∈-mapMaybe⁺ isInj₁ x refl) ∘ names⊆ ∘ n⊆ ∘ as⊆′ ∘ ∈-map⁺ inj₁
          where
            as⊆′ : map inj₁ as ⊆ names D
            as⊆′ rewrite remove-names {D} | eq = ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ˡ

        Bᵃʳ : (e : Arith) → secrets e ⊆ as → Script (Ctx (ς + m)) `ℤ
        Bᵃʳ (Arith.` x)    _   = ` x
        Bᵃʳ (Arith.∣ s ∣)  ⊆as = Script.∣ var (raise ς (L.Any.index (⊆as (here refl)))) ∣ `- ` (+ η)
        Bᵃʳ (x Arith.`+ y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
                              `+ Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
        Bᵃʳ (x Arith.`- y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
                              `- Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})

        Bᵖʳ : (e : Predicate) → secrets e ⊆ as → Script (Ctx (ς + m)) `Bool
        Bᵖʳ Predicate.`true    _   = `true
        Bᵖʳ (p Predicate.`∧ q) ⊆as = Bᵖʳ p (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names p} {names q})
                                  `∧ Bᵖʳ q (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names p) {names q})
        Bᵖʳ (Predicate.`¬ p)   ⊆as = `not (Bᵖʳ p ⊆as)
        Bᵖʳ (x Predicate.`= y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
                                  `= Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
        Bᵖʳ (x Predicate.`< y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
                                  `< Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
    ... | _ | _
        = Ctx ς , versig (mapWith∈ partG (K² D∈)) (allFin ς)


    Tᵢₙᵢₜ : ∃Tx¹
    Tᵢₙᵢₜ = -, record
      { inputs  = V.fromList $ (hashTxⁱ <$> codom txout₀)
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = V.[ -, record { value = V₀ ; validator = ƛ proj₂ (⋁ (mapWith∈ C₀ (Bout ∘ cs⊆))) } ]
      ; absLock = 0 }
      where
        cs⊆ : C₀ ⊆ subterms′ CS₀
        cs⊆ = subterms⊆ᶜˢ {ds = C₀}

    Tᵢₙᵢₜ♯ : ℤ
    Tᵢₙᵢₜ♯ = Tᵢₙᵢₜ ♯

    infix 0 _&_&_&_&_&_&_&_&_&_&_
    record State (c : ℂ) : Set where
      constructor _&_&_&_&_&_&_&_&_&_&_
      pattern
      field
        T,o  : TxInput
        curV : Value
        P    : ∃ (_⊆ partG)
        curT : Time

        p⊆ : participants c ⊆ partG

        s⊆ : subterms′ c ⊆ subterms′ CS₀
        ∃s : case c of λ{ (C _) → ∃ (_∈ subterms′ CS₀) ; _ → ⊤}

        sechash : Sechash c
        txout   : Txout c
        part    : Part c
        val     : Val c
    open State

    Return : ℂ → Set
    Return c = subterms⁺ c ↦′ ∃Txᶜ

    go : ∀ c → (∀ c′ → c′ ≺ c → State c′ → Return c′) → State c → Return c
    go (C c) f (T,o & v & (P , P⊆) & t & p⊆ & s⊆ & ∃s@(Dₚ , Dₚ∈) & sechash & txout & part & val)
      with c
    -- Bd
    ... | withdraw A = λ where
      (here refl) →
       -, sig⋆ V.[ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
         { inputs  = V.[ T,o ]
         ; wit     = wit⊥
         ; relLock = V.[ 0 ]
         ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ versig [ K {A} (p⊆ (here refl)) ] [ 0F ] } ]
         ; absLock = t }
    ... | A ⇒ d
        = f (C d) ≺-auth (T,o & v & (P \\ [ A ] , P⊆ ∘ \\-⊆) & t & p⊆ ∘ there & s⊆ & ∃s & sechash & txout & part & val)
    ... | after t′ ⇒ d
        = f (C d) ≺-after (T,o & v & (P , P⊆) & t ⊔ t′ & p⊆ & s⊆ & ∃s & sechash & txout & part & val)
    -- Bc
    ... | c′@(put zs &reveal as if p ⇒ cs) = λ where
      (here refl) → Tc
      (there x∈)  → f (CS cs) ≺-put
        ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
        & p⊆ & s⊆ & tt
        & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
        & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆)
        x∈
       where
        n⊆ : names cs ⊆ names c′
        n⊆ = ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ʳ (map inj₁ as)

        cs⊆ : cs ⊆ subterms′ CS₀
        cs⊆ = s⊆ ∘ subterms⊆ᶜˢ

        zs⊆ : zs ⊆ namesʳ c′
        zs⊆ = (λ x∈ → ∈-mapMaybe⁺ isInj₂ x∈ refl) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

        k = length zs

        ins : Vec TxInput k
        ins rewrite sym (length-mapWith∈ (setoid _) zs {f = hashTxⁱ ∘ txout ∘ zs⊆})
                  = V.fromList (mapWith∈ zs (hashTxⁱ ∘ txout ∘ zs⊆))

        K⋆ : zs ↦ List KeyPair
        K⋆ = [_] ∘ K ∘ proj₂ ∘ part ∘ zs⊆

        wits : Vec (List KeyPair) k
        wits rewrite sym (length-mapWith∈ (setoid _) zs {K⋆})
                   = V.fromList (mapWith∈ zs K⋆)

        Tc : ∃Tx¹
        Tc = suc k , sig⋆ (mapWith∈ P (K² Dₚ∈ ∘ P⊆) V.∷ wits) record
          { inputs  = T,o V.∷ ins
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.[ _ , record { value = v; validator = ƛ proj₂ (⋁ (mapWith∈ cs (Bout ∘ cs⊆))) } ]
          ; absLock = t }
        Tc♯ = Tc ♯
    -- Bpar
    ... | c′@(split vcs) = λ where
      (here refl) → Tc
      (there x∈)  → f (VCS vcs) ≺-split
        ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
        & p⊆ & s⊆ & tt
        & sechash & txout & part & val)
        x∈
       where
        Tc : ∃Txᶜ c′
        Tc = -, sig⋆ V.[ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
          { inputs  = V.[ T,o ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.Mem.mapWith∈ (V.fromList vcs) λ{ {vᵢ , Cᵢ} x∈ →
              let eᵢ = mapWith∈ Cᵢ (Bout ∘ s⊆ ∘ subterms⊆ᵛᶜˢ (V.Any.fromList⁻ x∈))
              in -, record { value = vᵢ ; validator = ƛ proj₂ (⋁ eᵢ) }
            }
          ; absLock = t }
        Tc♯ = Tc ♯

    go (CS x)  f st = ↦-∈  λ {d}  d∈  → f (C d)   (≺-∈ d∈)   (↓ st d∈)
      where
        ↓ : State (CS ds) → ds ↦′ (State ∘ C)
        ↓ {ds = d ∷ ds} (T,o & v & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val) (here refl)
          = T,o & v & P⊆ & t & p⊆ ∘ ∈-++⁺ˡ & s⊆′ & (d , s⊆ (here refl))
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆
          where
            n⊆ : names d ⊆ names (d ∷ ds)
            n⊆ = ∈-++⁺ˡ

            s⊆′ : subterms′ (C d) ⊆ subterms′ CS₀
            s⊆′ = s⊆ ∘ there ∘ ∈-++⁺ˡ
        ↓ {ds = d ∷ ds} (T,o & v & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val) (there x∈)
          = ↓ {ds = ds} (T,o & v & P⊆ & t
          & p⊆ ∘ (∈-++⁺ʳ _) & s⊆ ∘ ∈-++⁺ʳ _ & tt
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆) x∈
          where
            n⊆ : names ds ⊆ names (d ∷ ds)
            n⊆ = ∈-++⁺ʳ _
    go (VCS x) f st = ↦-∈ᵛ λ {cs} cs∈ → f (CS cs) (≺-∈ᵛ cs∈) (↓ᵛ st cs∈)
      where
        ↓ᵛ : State (VCS vcs) → map proj₂ vcs ↦′ (State ∘ CS)
        ↓ᵛ {vcs = (v , cs) ∷ vcs} (T,o & _ & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val) (here refl)
          = T,o & v & P⊆ & t & p⊆ ∘ ∈-++⁺ˡ & s⊆ ∘ ∈-++⁺ˡ & tt
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆
          where
            n⊆ : names cs ⊆ names ((v , cs) ∷ vcs)
            n⊆ = ∈-++⁺ˡ
        ↓ᵛ {vcs = (v , cs) ∷ vcs} ((T at o) & _ & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val) (there x∈)
          = ↓ᵛ {vcs = vcs} ((T at suc o) & v & P⊆ & t
          & p⊆ ∘ ∈-++⁺ʳ _ & s⊆ ∘ ∈-++⁺ʳ _ & tt
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆) x∈
          where
            n⊆ : names vcs ⊆ names ((v , cs) ∷ vcs)
            n⊆ = ∈-++⁺ʳ _
