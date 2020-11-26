{-# OPTIONS --allow-unsolved-metas #-}
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
open import Prelude.Set'
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

instance
  HP-ℂ : ∀ {X : Set} {{_ : Contract has X}} → ℂ has X
  HP-ℂ .collect (C d)     = collect d
  HP-ℂ .collect (CS ds)   = collect ds
  HP-ℂ .collect (VCS vcs) = collect vcs

participants-helperᶜˢ : participants (CS ds) ⊆ participants (put xs &reveal as if p ⇒ ds)
participants-helperᶜˢ {ds = d ∷ ds} d∈
  with ∈-++⁻ (participants d) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ d∈ˡ
... | inj₂ d∈ʳ = ∈-++⁺ʳ (participants d) (participants-helperᶜˢ {ds = ds} d∈ʳ)

participants-helperᵛᶜˢ : participants (VCS vcs) ⊆ participants (split vcs)
participants-helperᵛᶜˢ {vcs = (_ , ds) ∷ vcs} d∈ = {!!}
-- participants-helperᵛᶜˢ {vcs = (_ , ds) ∷ vcs} d∈
--   with ∈-++⁻ (participants ds) d∈
-- ... | inj₁ d∈ˡ = {!!} -- ∈-++⁺ˡ d∈ˡ
-- ... | inj₂ d∈ʳ = {!!} -- ∈-++⁺ʳ (participants ds) (participants-helperᵛᶜˢ {vcs = vcs} d∈ʳ)

nub-participants : Precondition → List Participant
nub-participants = nub ∘ participants

postulate
  nub-⊆⁻ : ∀ {A : Set} {{_ : DecEq A}} {xs : List A} → nub xs ⊆ xs
  nub-⊆⁺ : ∀ {A : Set} {{_ : DecEq A}} {xs : List A} → xs ⊆ nub xs
  \\-⊆ : ∀ {A : Set} {{_ : DecEq A}} {xs ys : List A} → xs \\ ys ⊆ xs

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
bitml-compiler {g = G₀} {ds = C₀} (_ , names⊆ , putComponents⊆ , _) sechash₀ txout₀ K K²₀
  = Tᵢₙᵢₜ , (≺-rec _ go) (CS C₀) record
      { T,o     = Tᵢₙᵢₜ♯ at 0
      ; curV    = V₀
      ; P       = partG , ⊆-refl
      ; curT    = 0
      ; p⊆      = nub-⊆⁺ ∘ p⊆₀
      ; K²      = K²₀
      ; sechash = weaken-↦ sechash₀ (mapMaybe-⊆ isInj₁ names⊆)
      ; txout   = weaken-↦ txout₀ (mapMaybe-⊆ isInj₂ names⊆)
      ; part    = weaken-↦ part₀ (mapMaybe-⊆ isInj₂ names⊆)
      ; val     = weaken-↦ val₀ (mapMaybe-⊆ isInj₂ names⊆) }
  where
    partG = nub-participants G₀
    ς     = length partG
    V₀    = sum (map (proj₁ ∘ proj₂) (persistentDeposits G₀))

    p⊆₀ : participants C₀ ⊆ participants G₀
    p⊆₀ = {!!} -- parts C₀ ⊆ parts C₀ ++ parts G₀ ⊆ persistentParts G₀ ⊆ parts G₀

    -- part: maps deposit names in G to the corresponding participant
    part₀ : namesʳ G₀ ↦ ∃ (_∈ partG)
    part₀ x∈ = proj₁ (getDeposit {g = G₀} x∈) , {!!}

    -- val: maps deposit names in G to the value contained in the deposit
    val₀ : namesʳ G₀ ↦ Value
    val₀ = proj₁ ∘ proj₂ ∘ getDeposit {g = G₀}

    -- Bout:
    Bout : subterms′ (CS C₀) ↦ ∃ (flip Script `Bool)
    Bout {D} D∈ with removeTopDecorations D | inspect removeTopDecorations D
    ... | put zs &reveal as if p ⇒ _ | ≡[ eq ]
        = Ctx (ς + m) , ( versig (mapWith∈ partG (K²₀ D∈)) (map (inject+ m) (allFin ς))
                     `∧ Bᵖʳ p p⊆as
                     `∧ ⋀ (mapEnumWith∈ as (λ i a a∈ →
                             let bi = var (raise ς i)
                             in (hash bi `= ` (sechash₀ (as⊆ a∈))) `∧ (` (+ η) `< Script.∣ bi ∣)))
                        )
          where
            m : ℕ
            m = length as

            p⊆ : putComponents D ⊆ putComponents C₀
            p⊆ = subterms′-putComponents⊆ {ds = C₀} D∈

            n⊆ : names D ⊆ names C₀
            n⊆ = subterms′-names⊆ {d = D} {ds = C₀} D∈

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
        = Ctx ς , versig (mapWith∈ partG (K²₀ D∈)) (allFin ς)


    Tᵢₙᵢₜ : ∃Tx
    Tᵢₙᵢₜ = -, -, record
      { inputs  = V.fromList (mapWith∈ (persistentDeposits G₀) (txout₀ ∘ getName {g = G₀}))
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = V.[ -, record { value = V₀ ; validator = ƛ (proj₂ (⋁ (mapWith∈ C₀ (Bout ∘ cs⊆)))) } ]
      ; absLock = 0 }
      where
        cs⊆ : C₀ ⊆ subterms′ (CS C₀)
        cs⊆ = {!!}

    Tᵢₙᵢₜ♯ = hashTx Tᵢₙᵢₜ

    record State (c : ℂ) : Set where
      constructor _&_&_&_&_&_&_&_&_&_
      field
        T,o  : TxInput
        curV : Value
        P    : ∃ (_⊆ partG)
        curT : Time
        --
        p⊆ : participants c ⊆ partG

        --
        K²      : subterms′ c ↦ (partG ↦ KeyPair)
        sechash : namesˡ c ↦ ℤ
        txout   : namesʳ c ↦ TxInput
        part    : namesʳ c ↦ ∃ (_∈ partG)
        val     : namesʳ c ↦ Value
    open State

    Return : ℂ → Set
    Return c = subterms⁺ c ↦ ∃Tx

    ↓ : State (CS ds) → ds ↦′ (State ∘ C)
    ↓ {ds = d ∷ ds} (T,o & v & P⊆ & t & p⊆ & K² & sechash & txout & part & val) (here refl)
      = T,o & v & P⊆ & t & (p⊆ ∘ ∈-++⁺ˡ) & weaken-↦ K² {!!} {-∈-++⁺ˡ-}
      & weaken-↦ sechash (mapMaybe-⊆ isInj₁ n⊆) & weaken-↦ txout (mapMaybe-⊆ isInj₂ n⊆)
      & weaken-↦ part (mapMaybe-⊆ isInj₂ n⊆) & weaken-↦ val (mapMaybe-⊆ isInj₂ n⊆)
      where
        n⊆ : names d ⊆ names (d ∷ ds)
        n⊆ = ∈-++⁺ˡ
    ↓ {ds = d ∷ ds} (T,o & v & P⊆ & t & p⊆ & K² & sechash & txout & part & val) (there x∈)
      = ↓ {ds = ds} (T,o & v & P⊆ & t
      & (p⊆ ∘ (∈-++⁺ʳ _)) & weaken-↦ K² (∈-++⁺ʳ _)
      & weaken-↦ sechash (mapMaybe-⊆ isInj₁ n⊆) & weaken-↦ txout (mapMaybe-⊆ isInj₂ n⊆)
      & weaken-↦ part (mapMaybe-⊆ isInj₂ n⊆) & weaken-↦ val (mapMaybe-⊆ isInj₂ n⊆)) x∈
      where
        n⊆ : names ds ⊆ names (d ∷ ds)
        n⊆ = ∈-++⁺ʳ _

    ↓ᵛ : State (VCS vcs) → map proj₂ vcs ↦′ (State ∘ CS)
    ↓ᵛ {vcs = (v , cs) ∷ vcs} (T,o & _ & P⊆ & t & p⊆ & K² & sechash & txout & part & val) (here refl)
      = T,o & v & P⊆ & t & (p⊆ ∘ ∈-++⁺ˡ) & weaken-↦ K² ∈-++⁺ˡ
      & weaken-↦ sechash (mapMaybe-⊆ isInj₁ n⊆) & weaken-↦ txout (mapMaybe-⊆ isInj₂ n⊆)
      & weaken-↦ part (mapMaybe-⊆ isInj₂ n⊆) & weaken-↦ val (mapMaybe-⊆ isInj₂ n⊆)
      where
        n⊆ : names cs ⊆ names ((v , cs) ∷ vcs)
        n⊆ = ∈-++⁺ˡ
    ↓ᵛ {vcs = (v , cs) ∷ vcs} ((T at o) & _ & P⊆ & t & p⊆ & K² & sechash & txout & part & val) (there x∈)
      = ↓ᵛ {vcs = vcs} ((T at suc o) & v & P⊆ & t
      & (p⊆ ∘ (∈-++⁺ʳ _)) & weaken-↦ K² (∈-++⁺ʳ _)
      & weaken-↦ sechash (mapMaybe-⊆ isInj₁ n⊆) & weaken-↦ txout (mapMaybe-⊆ isInj₂ n⊆)
      & weaken-↦ part (mapMaybe-⊆ isInj₂ n⊆) & weaken-↦ val (mapMaybe-⊆ isInj₂ n⊆)) x∈
      where
        n⊆ : names vcs ⊆ names ((v , cs) ∷ vcs)
        n⊆ = ∈-++⁺ʳ _

    go : ∀ c → (∀ c′ → c′ ≺ c → State c′ → Return c′) → State c → Return c
    go (C c) f (T,o & v & (P , P⊆) & t & p⊆ & K² & sechash & txout & part & val)
      with c
    -- Bd
    ... | withdraw A = λ
      {(here refl) →
        -, -, sig⋆ V.[ mapWith∈ P {!(K² {-(here refl)-} ∘ P⊆)!} ] record
          { inputs  = V.[ T,o ]
          ; wit     = wit⊥
          ; relLock = V.[ 0 ]
          ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ (versig [ K {A} (p⊆ (here refl)) ] [ 0F ]) } ]
          ; absLock = t }
      }
    ... | A ⇒ d
        = f (C d) ≺-auth (T,o & v & (P \\ [ A ] , P⊆ ∘ \\-⊆)
        & t & (p⊆ ∘ there) & K² & sechash & txout & part & val)
    ... | after t′ ⇒ d
        = f (C d) ≺-after (T,o & v & (P , P⊆) & t ⊔ t′ & p⊆ & K² & sechash & txout & part & val)
    -- Bc
    ... | c′@(put zs &reveal as if _ ⇒ cs) = λ
      { (here refl) → Tc
      ; (there x∈)  → f (CS cs) ≺-put
          ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
          & (p⊆ ∘ participants-helperᶜˢ {ds = cs}) & weaken-↦ K² {!!} {-there-}
          & weaken-↦ sechash (mapMaybe-⊆ isInj₁ n⊆) & weaken-↦ txout (mapMaybe-⊆ isInj₂ n⊆)
          & weaken-↦ part (mapMaybe-⊆ isInj₂ n⊆) & weaken-↦ val (mapMaybe-⊆ isInj₂ n⊆))
          x∈
      }
      where
        n⊆ : names cs ⊆ names c′
        n⊆ = ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ʳ (map inj₁ as)

        zs⊆ : zs ⊆ namesʳ c′
        zs⊆ = (λ x∈ → ∈-mapMaybe⁺ isInj₂ x∈ refl) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

        cs⊆ : cs ⊆ subterms′ (CS C₀)
        cs⊆ = {!!}

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
        Tc = suc k , -, sig⋆ (mapWith∈ P (K² {!!} {-(here refl)-} ∘ P⊆) V.∷ wits) record
          { inputs  = T,o V.∷ ins
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.[ _ , record { value = v; validator = ƛ (proj₂ (⋁ (mapWith∈ cs (Bout ∘ cs⊆)))) } ]
          ; absLock = t }
        Tc♯ = hashTx Tc
    -- Bpar
    ... | c′@(split vcs) = λ
      { (here refl) → Tc
      ; (there x∈)  → f (VCS vcs) ≺-split
          ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
          & (p⊆ ∘ participants-helperᵛᶜˢ {vcs = vcs}) & weaken-↦ K² {!!} {-there-}
          & sechash & txout & part & val)
          x∈
      }
      where
        Cᵢ⊆ : ∀ {v cs} → (v , cs) ∈ vcs → cs ⊆ subterms′ (CS C₀)
        Cᵢ⊆ = {!!}

        eᵢⱼ : List (Value × List (∃ (flip Script `Bool)))
        eᵢⱼ = mapWith∈ vcs λ{ {v , Cᵢ} x∈ → v , mapWith∈ Cᵢ (Bout ∘ Cᵢ⊆ x∈) }

        Tc : ∃Tx
        Tc = -, -, sig⋆ V.[ mapWith∈ P (K² {!!} {-(here refl)-} ∘ P⊆) ] record
          { inputs  = V.[ T,o ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.map (λ{ (vᵢ , eᵢ) → -, record { value = vᵢ ; validator = ƛ (proj₂ (⋁ eᵢ)) }})
                            (V.fromList eᵢⱼ)
          ; absLock = t }
        Tc♯ = hashTx Tc

    go (CS x) f  st = ↦-∈  λ {d}  d∈  → f (C d)   (≺-∈ d∈)   (↓ st d∈)
    go (VCS x) f st = ↦-∈ᵛ λ {cs} cs∈ → f (CS cs) (≺-∈ᵛ cs∈) (↓ᵛ st cs∈)

{-
bitml-compiler :
    -- the input contract & precondition
    (ad : Advertisement)
    -- only compile valid advertisements
  → ValidAdvertisement ad
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (namesˡ ad ↦ ℤ)
    -- txout: maps deposits in G to *pre-existing* transactions with the corresponding value
  → (namesʳ ad ↦ TxInput)
    -- Exchanged keypairs K(A) and K(D,A)
  → (Participant → KeyPair)
  → (Contract → Participant → KeyPair)
    -- a set of transactions to be submitted
  → List⁺ ∃Tx
bitml-compiler (⟨ G₀ ⟩ C₀) (_ , names⊆ , putComponents⊆ , _) sechash txout K K²
  = Tᵢₙᵢₜ
  ∷ concat (map-⊆ C₀ (⊆ᶜ-refl C₀) λ Dᵢ Dᵢ⊆C₀ →
      Bd Dᵢ (≺-wf (C Dᵢ)) Dᵢ⊆C₀ Dᵢ Tᵢₙᵢₜ♯ 0 V partG 0)
  where
    partG : List Participant
    partG = nub (participants G₀)

    -- part: maps deposit names in G to the corresponding participant
    part : ∀ {x} → inj₂ x ∈ names G₀ → Participant
    part = proj₁ ∘ getDeposit {g = G₀}

    -- val: maps deposit names in G to the value contained in the deposit
    val : namesʳ G₀ ↦ Value
    val = proj₁ ∘ proj₂ ∘ getDeposit {g = G₀}

    -- K(D,ℙ): abbreviation for keys coming from multiple participant
    K⋆ : Contract → List Participant → List KeyPair
    K⋆ D = map (K² D)

    ς : ℕ
    ς = length partG

    V : Value
    V = sum (map (proj₁ ∘ proj₂) (persistentDeposits G₀))

    Bout : (d : Contract)
         → (d ⊆ᶜ C₀)
         → ∃[ ctx ] Script ctx `Bool
    Bout D (p⊆ & n⊆) with removeTopDecorations D | inspect removeTopDecorations D
    ... | put zs &reveal as if p ⇒ _ | ≡[ eq ]
        = Ctx (ς + m) , ( versig (K⋆ D partG) (map (inject+ m) (allFin ς))
                     `∧ Bᵖʳ p p⊆as
                     `∧ ⋀ (mapEnumWith∈ as (λ i a a∈ →
                             let bi = var (raise ς i)
                             in (hash bi `= ` (sechash (as⊆ a∈))) `∧ (` (+ η) `< Script.∣ bi ∣)))
                        )
          where
            m : ℕ
            m = length as

            put∈ : (zs , as , p) ∈ putComponents D
            put∈ rewrite remove-putComponents {D} | eq = here refl

            p⊆as : secrets p ⊆ as
            p⊆as = proj₂ (lookup putComponents⊆ (p⊆ put∈))

            as⊆ : ∀ {a} → a ∈ as → inj₁ a ∈ names G₀
            as⊆ rewrite remove-names {D} | eq = names⊆ ∘ n⊆ ∘ ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₁

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
        = Ctx ς , versig (K⋆ D partG) (allFin ς)

    Tᵢₙᵢₜ : ∃Tx
    Tᵢₙᵢₜ = _
          , _
          , record { inputs  = V.fromList (mapWith∈ (persistentDeposits G₀) (txout ∘ getName {g = G₀}))
                   ; wit     = wit⊥
                   ; relLock = V.replicate 0
                   ; outputs = V.[ _ , record { value     = V
                                              ; validator = ƛ (proj₂ (⋁ (map-⊆ C₀ (⊆ᶜ-refl C₀) Bout))) } ]
                   ; absLock = 0 }
    Tᵢₙᵢₜ♯ = hashTx Tᵢₙᵢₜ

    Bc : (c : Contracts) → Acc _≺_ (CS c) → c ⊆ᶜ C₀
       → Contract → HashId → ℕ
       → Value → Σ[ I ∈ Ids ] (∀ {i} → i ∈ I → inj₂ i ∈ names G₀)
       → List Participant → Time
       → List ∃Tx

    Bd : (d : Contract) → Acc _≺_ (C d) → d ⊆ᶜ C₀
       → Contract → HashId → ℕ
       → Value
       → List Participant → Time
       → List ∃Tx

    Bpar : (vcs : VContracts) → Acc _≺_ (VCS vcs) → vcs ⊆ᶜ C₀
         → Contract → HashId → ℕ
         → List Participant → Time
         → List ∃Tx

    Bd (put zs &reveal as if _ ⇒ c) (acc a) (p⊆ & n⊆) Dₚ T o v P t
      = Bc c (a _ refl) C⊆C₀ Dₚ T o (v + sum (mapWith∈ zs (val ∘ zs⊆))) zs′ P t
          where
            C⊆C₀ : c ⊆ᶜ C₀
            C⊆C₀ = (p⊆ ∘ ∈-++⁺ʳ _) & (n⊆ ∘ ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ʳ (map inj₁ as))

            zs′ : Σ[ I ∈ Ids ] (∀ {i} → i ∈ I → inj₂ i ∈ names G₀)
            zs′ = zs , λ z∈ → names⊆ (n⊆ (∈-++⁺ˡ (∈-map⁺ inj₂ z∈)))

            zs⊆ : ∀ {z} → z ∈ zs → inj₂ z ∈ names G₀
            zs⊆ = names⊆ ∘ n⊆ ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

    Bd (withdraw A) _ _ Dₚ T o v P t
      = [ _
        , _
        , sig⋆ V.[ K⋆ Dₚ P ]
               (record { inputs  = V.[ T at 0 ]
                       ; wit     = wit⊥
                       ; relLock = V.[ 0 ]
                       ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ (versig [ K A ] [ 0F ]) } ]
                       ; absLock = t })
        ]
    Bd (split Cs) (acc a) (p⊆ & n⊆) Dₚ T o v P t
      = if ⌊ sum (map proj₁ Cs) ≤? v ⌋ then []
                                       else Bpar Cs (a _ refl) (p⊆ & n⊆) Dₚ T o P t
    Bd (A ⇒ D′) (acc a) (p⊆ & n⊆) Dₚ T o v P t
      = Bd D′ (a _ refl) (p⊆ & n⊆) Dₚ T o v (P \\ [ A ]) t
    Bd (after t′ ⇒ D′) (acc a) (p⊆ & n⊆) Dₚ T o v P t
      = Bd D′ (a _ refl) (p⊆ & n⊆) Dₚ T o v P (t ⊔ t′)

    Bc c (acc a) C⊆C₀ Dₚ T o v (I , I⊆) P t
      = Tc
      ∷ concat (map∈-⊆ c C⊆C₀ λ {Dᵢ} Dᵢ∈ Dᵢ⊆C₀ →
          Bd Dᵢ (a _ Dᵢ∈) Dᵢ⊆C₀ Dᵢ Tc♯ 0 v partG t)
      where
        k = length I

        ins : Vec TxInput k
        ins rewrite sym (length-mapWith∈ (setoid _) I {f = txout ∘ I⊆})
                  = V.fromList (mapWith∈ I (txout ∘ I⊆))

        wits : Vec (List KeyPair) k
        wits rewrite sym (length-mapWith∈ (setoid _) I {[_] ∘ K ∘ part ∘ I⊆})
                   = V.fromList (mapWith∈ I ([_] ∘ K ∘ part ∘ I⊆))

        Tc : ∃Tx
        Tc = suc k
           , _
           , sig⋆ (K⋆ Dₚ P V.∷ wits)
                  (record { inputs  = T at o V.∷ ins
                          ; wit     = wit⊥
                          ; relLock = V.replicate 0
                          ; outputs = V.[ _ , record { value     = v
                                                     ; validator = ƛ (proj₂ (⋁ (map-⊆ c C⊆C₀ Bout))) } ]
                          ; absLock = t })
        Tc♯ = hashTx Tc


    Bpar vcs (acc a) vcs⊆C₀ Dₚ T o P t
      = Tc
      ∷ Tᵢⱼ
      where
        eᵢⱼ : List (Value × List (∃[ ctx ] Script ctx `Bool))
        eᵢⱼ = map-⊆ vcs vcs⊆C₀ λ{ (v , Cᵢ) (p⊆ & n⊆) →
                v , map-⊆ Cᵢ (p⊆ & n⊆) Bout }

        Tc : ∃Tx
        Tc = _
           , _
           , sig⋆ V.[ K⋆ Dₚ P ]
                  (record { inputs  = V.[ T at o ]
                          ; wit     = wit⊥
                          ; relLock = V.replicate 0
                          ; outputs = V.map (λ{ (vᵢ , eᵢ) → _ , record { value     = vᵢ
                                                                       ; validator = ƛ (proj₂ (⋁ eᵢ)) }})
                                            (V.fromList eᵢⱼ)
                          ; absLock = t })
        Tc♯ = hashTx Tc

        Tᵢⱼ : List ∃Tx
        Tᵢⱼ = concat (map∈-⊆ vcs vcs⊆C₀ λ{ {vᵢ , Cᵢ} Cᵢ∈ (p⊆ & n⊆) →
                concat (map∈-⊆ Cᵢ (p⊆ & n⊆) λ {Dᵢⱼ} Dᵢⱼ∈ Dᵢⱼ⊆C₀  →
                  Bd Dᵢⱼ (a _ (Cᵢ , Dᵢⱼ∈ , ∈-map⁺ proj₂ Cᵢ∈)) Dᵢⱼ⊆C₀ Dᵢⱼ Tc♯ (toℕ $ index Cᵢ∈) vᵢ partG 0)})
-}
