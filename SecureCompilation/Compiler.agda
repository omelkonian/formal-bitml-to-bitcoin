----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------

open import Data.Fin as Fin using (raise; inject+; toℕ)
open import Data.Nat.Properties using (≤-refl; <-trans; n<1+n)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.Setoid.Properties         using (length-mapWith∈)
open import Data.List.Relation.Unary.Any                   using (index)
open import Data.List.Relation.Unary.All                   using (lookup)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)

open import Relation.Binary.PropositionalEquality using (setoid)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections

-- Bitcoin
open import Bitcoin.BasicTypes
  using (HashId)
open import Bitcoin.Crypto
  using (KeyPair)
open import Bitcoin.Script.Base
  using ( ty; ScriptType; `Bool; `ℤ
        ; ctx; Ctx; ScriptContext
        ; var; `; _`+_; _`-_; _`=_; _`<_; `if_then_else_; hash; versig; absAfter_⇒_; relAfter_⇒_; Script
        ; _`∧_; `true; _`∨_; `false; `not
        ; ƛ_; BitcoinScript; ∃BitcoinScript
        ; {-∣_∣;-} ⋁; ⋀ )
open import Bitcoin.Tx.Base
  using ( _at_; TxInput
        ; Tx; ∃Tx
        ; Witness; ∃Witness )
open import Bitcoin.Tx.Crypto
  using (hashTx; sig⋆; wit⊥)

module SecureCompilation.Compiler

  -- BitML parameters
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)

  -- Compilation parameters
  (η : ℕ) -- public security nonce η, ensures adversaries cannot guess
  where

-- BitML
open import BitML.BasicTypes
  using ( Secret; Time; Value; Values; Id; Ids; Name; Names
        ; {-variables-} v; x; xs; as; t )
open import BitML.Predicate
  using ( Predicate; Arith
        ; {-variables-} p )
open import BitML.Contracts.Types Participant Honest
  using ( Contract; Contracts; VContracts
        ; put_&reveal_if_⇒_; withdraw; split; _⇒_; after_⇒_
        ; Precondition
        ; ⟨_⟩_; Advertisement; G
        ; {-variables-} A; g; d; d′; ds; ds′; vcs )
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Contracts.Induction Participant Honest
open import BitML.Contracts.Validity Participant Honest

bitml-compiler :
    -- the input contract & precondition (only compile valid advertisements)
    ValidAdvertisement (⟨ g ⟩ ds)
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (sechash : namesˡ g ↦ ℤ)
    -- txout: maps deposits in G to *pre-existing* transactions with the corresponding value
  → (txout : namesʳ g ↦ TxInput)
    -- Exchanged keypairs K(A) and K(D,A)
  → let partG = nub-participants g in
    (K : partG ↦ KeyPair)
  → (K² : subterms′ (CS ds) ↦ (partG ↦ KeyPair))
    -- a set of transactions to be submitted
  → ∃Tx × (subterms⁺ (CS ds) ↦ ∃Tx)
bitml-compiler {g = G₀} {ds = C₀} (_ , names⊆ , putComponents⊆ , part⊆) sechash₀ txout₀ K K²
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
    p⊆₀ = persistent⊆ {G₀} ∘ part⊆ ∘ ∈-++⁺ʳ (participants G₀)

    -- part: maps deposit names in G to the corresponding participant
    part₀ : namesʳ G₀ ↦ ∃ (_∈ partG)
    part₀ x∈ = _ , ∈-nub⁺ (proj₂ (getDeposit {g = G₀} x∈))

    -- val: maps deposit names in G to the value contained in the deposit
    val₀ : namesʳ G₀ ↦ Value
    val₀ = proj₁ ∘ proj₂ ∘ proj₁ ∘ getDeposit {g = G₀}

    -- Bout:
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
            Bᵃʳ (Arith.∣ s ∣)  ⊆as = Script.∣ var (raise ς (index (⊆as (here refl)))) ∣ `- ` (+ η)
            Bᵃʳ (x Arith.`+ y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `+ Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
            Bᵃʳ (x Arith.`- y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `- Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)

            Bᵖʳ : (e : Predicate) → secrets e ⊆ as → Script (Ctx (ς + m)) `Bool
            Bᵖʳ Predicate.`true     _   = `true
            Bᵖʳ (p Predicate.`∧ p′) ⊆as = Bᵖʳ p (⊆as ∘ ∈-++⁺ˡ) `∧ Bᵖʳ p′ (⊆as ∘ ∈-++⁺ʳ _)
            Bᵖʳ (Predicate.`¬ p)    ⊆as = `not (Bᵖʳ p ⊆as)
            Bᵖʳ (x Predicate.`= y)  ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `= Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
            Bᵖʳ (x Predicate.`< y)  ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `< Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
    ... | _ | _
        = Ctx ς , versig (mapWith∈ partG (K² D∈)) (allFin ς)


    Tᵢₙᵢₜ : ∃Tx
    Tᵢₙᵢₜ = -, -, record
      { inputs  = V.fromList (codom txout₀)
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = V.[ -, record { value = V₀ ; validator = ƛ proj₂ (⋁ (mapWith∈ C₀ (Bout ∘ cs⊆))) } ]
      ; absLock = 0 }
      where
        cs⊆ : C₀ ⊆ subterms′ CS₀
        cs⊆ = subterms⊆ᶜˢ {ds = C₀}

    Tᵢₙᵢₜ♯ = hashTx Tᵢₙᵢₜ

    infix 0 _&_&_&_&_&_&_&_&_&_&_
    record State (c : ℂ) : Set where
      constructor _&_&_&_&_&_&_&_&_&_&_
      field
        T,o  : TxInput
        curV : Value
        P    : ∃ (_⊆ partG)
        curT : Time

        p⊆ : participants c ⊆ partG

        -- Bout : subterms′ c ↦ (∃[ ctx ] Script ctx `Bool)
        -- K²   : subterms′ c ↦ (partG ↦ KeyPair)
        s⊆ : subterms′ c ⊆ subterms′ CS₀
        ∃s : case c of λ{ (C _) → ∃ (_∈ subterms′ CS₀) ; _ → ⊤}

        sechash : namesˡ c ↦ ℤ
        txout   : namesʳ c ↦ TxInput
        part    : namesʳ c ↦ ∃ (_∈ partG)
        val     : namesʳ c ↦ Value
    open State

    Return : ℂ → Set
    Return c = subterms⁺ c ↦ ∃Tx

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

    go : ∀ c → (∀ c′ → c′ ≺ c → State c′ → Return c′) → State c → Return c
    go (C c) f (T,o & v & (P , P⊆) & t & p⊆ & s⊆ & ∃s@(Dₚ , Dₚ∈) & sechash & txout & part & val)
      with c
    -- Bd
    ... | withdraw A = λ
      {(here refl) →
        -, -, sig⋆ V.[ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
          { inputs  = V.[ T,o ]
          ; wit     = wit⊥
          ; relLock = V.[ 0 ]
          ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ versig [ K {A} (p⊆ (here refl)) ] [ 0F ] } ]
          ; absLock = t }
      }
    ... | A ⇒ d
        = f (C d) ≺-auth (T,o & v & (P \\ [ A ] , P⊆ ∘ \\-⊆) & t & p⊆ ∘ there & s⊆ & ∃s & sechash & txout & part & val)
    ... | after t′ ⇒ d
        = f (C d) ≺-after (T,o & v & (P , P⊆) & t ⊔ t′ & p⊆ & s⊆ & ∃s & sechash & txout & part & val)
    -- Bc
    ... | c′@(put zs &reveal as if p ⇒ cs) = λ
      { (here refl) → Tc
      ; (there x∈)  → f (CS cs) ≺-put
          ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
          & p⊆ & s⊆ & tt
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆)
          x∈
      }
      where
        n⊆ : names cs ⊆ names c′
        n⊆ = ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ʳ (map inj₁ as)

        cs⊆ : cs ⊆ subterms′ CS₀
        cs⊆ = s⊆ ∘ subterms⊆ᶜˢ

        zs⊆ : zs ⊆ namesʳ c′
        zs⊆ = (λ x∈ → ∈-mapMaybe⁺ isInj₂ x∈ refl) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

        k = length zs

        ins : Vec TxInput k
        ins rewrite sym (length-mapWith∈ (setoid _) zs {f = txout ∘ zs⊆})
                  = V.fromList (mapWith∈ zs (txout ∘ zs⊆))

        K⋆ : zs ↦ List KeyPair
        K⋆ = [_] ∘ K ∘ proj₂ ∘ part ∘ zs⊆

        wits : Vec (List KeyPair) k
        wits rewrite sym (length-mapWith∈ (setoid _) zs {K⋆})
                   = V.fromList (mapWith∈ zs K⋆)

        Tc : ∃Tx
        Tc = suc k , -, sig⋆ (mapWith∈ P (K² Dₚ∈ ∘ P⊆) V.∷ wits) record
          { inputs  = T,o V.∷ ins
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.[ _ , record { value = v; validator = ƛ proj₂ (⋁ (mapWith∈ cs (Bout ∘ cs⊆))) } ]
          ; absLock = t }
        Tc♯ = hashTx Tc
    -- Bpar
    ... | c′@(split vcs) = λ
      { (here refl) → Tc
      ; (there x∈)  → f (VCS vcs) ≺-split
          ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
          & p⊆ & s⊆ & tt
          & sechash & txout & part & val)
          x∈
      }
      where
        eᵢⱼ : List (Value × List (∃[ ctx ] Script ctx `Bool))
        eᵢⱼ = mapWith∈ vcs λ{ {v , Cᵢ} x∈ → v , mapWith∈ Cᵢ (Bout ∘ s⊆ ∘ subterms⊆ᵛᶜˢ x∈) }

        Tc : ∃Tx
        Tc = -, -, sig⋆ V.[ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
          { inputs  = V.[ T,o ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.map (λ{ (vᵢ , eᵢ) → -, record { value = vᵢ ; validator = ƛ proj₂ (⋁ eᵢ) }})
                            (V.fromList eᵢⱼ)
          ; absLock = t }
        Tc♯ = hashTx Tc

    go (CS x) f  st = ↦-∈  λ {d}  d∈  → f (C d)   (≺-∈ d∈)   (↓ st d∈)
    go (VCS x) f st = ↦-∈ᵛ λ {cs} cs∈ → f (CS cs) (≺-∈ᵛ cs∈) (↓ᵛ st cs∈)
