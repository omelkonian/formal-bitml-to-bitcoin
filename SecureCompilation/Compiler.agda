----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------

open import Data.Fin as Fin using (raise; inject+; toℕ)


open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Lists
open import Prelude.Lists.Dec
open L.Mem
open import Prelude.DecEq
open import Prelude.Sets hiding (codom; _↦_; _↦′_)
open import Prelude.Lists.Collections
open import Prelude.Functor
open import Prelude.Validity

open import Bitcoin hiding (Value; Time)

open import BitML.BasicTypes using (⋯)

module SecureCompilation.Compiler

  -- BitML parameters
  (⋯ : ⋯) (let open ⋯ ⋯)

  -- Compilation parameters
  (η : ℕ) -- public security nonce η, ensures adversaries cannot guess
  where

open import BitML ⋯ hiding (C; `_; _`+_; _`-_; `true)
open Induction renaming (D to 𝔻)

open import SecureCompilation.Mappings ⋯

-- single-output transactions
Tx¹ : ℕ → Type
Tx¹ i = Tx i 1
∃Tx¹ = ∃ Tx¹

-- contract-dependent outputs
outputLen : Branch → ℕ
outputLen (split vcs) = length vcs
outputLen _           = 1

Txᶜ : ℕ → Branch → Type
Txᶜ i c = Tx i (outputLen c)

∃Txᶜ : Branch → Type
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
bitml-compiler {ad = ⟨ G₀ ⟩ C₀}
  (record { names-⊆ = record {unmk⊆ = names⊆}
          ; names-put = putComponents⊆
          ; parts-⊆ = record {unmk⊆ = part⊆}
          })
  sechash₀ txout₀ K K²
  = Tᵢₙᵢₜ , (≺-rec _ go) C₀′ record
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
    C₀′   = C C₀
    partG = nub-participants G₀
    ς     = length partG
    V₀    = sum (map (proj₁ ∘ proj₂) (persistentDeposits G₀))

    p⊆₀ : participants C₀ ⊆ participants G₀
    p⊆₀ = persistentParticipants⊆ {G₀} ∘ part⊆ ∘ ∈-++⁺ʳ (participants G₀)

    -- part: maps deposit names in G to the corresponding participant
    part₀ : namesʳ G₀ ↦ ∃ (_∈ partG)
    part₀ = -,_ ∘ ∈-nub⁺ ∘ proj₂ ∘ getDeposit {g = G₀}

    private variable X : Type

    Part : ⦃ _ : X has Name ⦄ → Pred₀ X
    Part x = namesʳ x ↦ ∃ (_∈ partG)

    -- val: maps deposit names in G to the value contained in the deposit
    val₀ : namesʳ G₀ ↦ Value
    val₀ = proj₁ ∘ proj₂ ∘ proj₁ ∘ getDeposit {g = G₀}

    Val : ⦃ _ : X has Name ⦄ → Pred₀ X
    Val x = namesʳ x ↦ Value

    -- Bout
    Bout : subterms′ C₀′ ↦ (∃[ ctx ] Script ctx `Bool)
    Bout {D} D∈ with removeTopDecorations D | inspect removeTopDecorations D
    ... | put zs &reveal as if p ⇒ _ | ≡[ eq ]
        = (ς + m) , ( versig (mapWith∈ partG (K² D∈)) (map (inject+ m) (allFin ς))
                    Bitcoin.`∧ Bᵖʳ p p⊆as
                    Bitcoin.`∧ ⋀ (mapEnumWith∈ as (λ i a a∈ →
                      let bi = var (raise ς i)
                      in (hash bi Bitcoin.`= ` (sechash₀ (as⊆ a∈))) Bitcoin.`∧ (` (+ η) Bitcoin.`< Script.∣ bi ∣)))
                    )
      where
        m : ℕ
        m = length as

        p⊆ : putComponents D ⊆ putComponents C₀
        p⊆ = subterms′-putComponents⊆ᶜ {ds = C₀} D∈

        n⊆ : names D ⊆ names C₀
        n⊆ = subterms′-names⊆ᶜ {d = D} {ds = C₀} D∈

        put∈ : (zs , as , p) ∈ putComponents D
        put∈ rewrite remove-putComponents {D} | eq = here refl

        p⊆as : secrets p ⊆ as
        p⊆as = L.All.lookup putComponents⊆ (p⊆ put∈) .proj₂ .unmk⊆

        as⊆ : as ⊆ namesˡ G₀
        as⊆ = (λ x → ∈-mapMaybe⁺ isInj₁ x refl) ∘ names⊆ ∘ n⊆ ∘ as⊆′ ∘ ∈-map⁺ inj₁
          where
            as⊆′ : map inj₁ as ⊆ names D
            as⊆′ rewrite remove-names {D} | eq = ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ˡ

        Bᵃʳ : (e : Arith) → secrets e ⊆ as → Script (ς + m) `ℤ
        Bᵃʳ (Arith.｀ x)    _   = ` x
        Bᵃʳ (Arith.∥ s ∥)  ⊆as =
          Script.∣_∣ (var $ raise ς $ L.Any.index $ ⊆as $ here refl) `- ` (+ η)
        Bᵃʳ (x Arith.`+ y) ⊆as =
             Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
          `+ Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
        Bᵃʳ (x Arith.`- y) ⊆as =
             Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
          `- Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})

        Bᵖʳ : (e : Predicate) → secrets e ⊆ as → Script (ς + m) `Bool
        Bᵖʳ Predicate.`true    _   = `true
        Bᵖʳ (p Predicate.`∧ q) ⊆as = Bᵖʳ p (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names p} {names q})
                                  Bitcoin.`∧ Bᵖʳ q (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names p) {names q})
        Bᵖʳ (Predicate.`¬ p)   ⊆as = `not (Bᵖʳ p ⊆as)
        Bᵖʳ (x Predicate.`= y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
                                  Bitcoin.`= Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
        Bᵖʳ (x Predicate.`< y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
                                  Bitcoin.`< Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
    ... | _ | _
        = ς , versig (mapWith∈ partG (K² D∈)) (allFin ς)


    Tᵢₙᵢₜ : ∃Tx¹
    Tᵢₙᵢₜ = -, record
      { inputs  = V.fromList $ (hashTxⁱ <$> codom txout₀)
      ; wit     = wit⊥
      ; relLock = V.replicate 0
      ; outputs = [ -, record { value = V₀ ; validator = ƛ proj₂ (⋁ (mapWith∈ C₀ (Bout ∘ cs⊆))) } ]
      ; absLock = 0 }
      where
        cs⊆ : C₀ ⊆ subterms′ C₀′
        cs⊆ = subterms⊆ᶜ {ds = C₀}
    Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ .proj₂) ♯

    infix 0 _&_&_&_&_&_&_&_&_&_&_
    record State (c : ℂ) : Type where
      constructor _&_&_&_&_&_&_&_&_&_&_
      pattern
      field
        T,o  : TxInput
        curV : Value
        P    : ∃ (_⊆ partG)
        curT : Time

        p⊆ : participants c ⊆ partG

        s⊆ : subterms′ c ⊆ subterms′ C₀′
        ∃s : case c of λ{ (𝔻 _) → ∃ (_∈ subterms′ C₀′) ; _ → ⊤}

        sechash : Sechash c
        txout   : Txout c
        part    : Part c
        val     : Val c
    open State

    Return : ℂ → Type
    Return c = subterms⁺ c ↦′ ∃Txᶜ

    go : ∀ c → (∀ c′ → c′ ≺ c → State c′ → Return c′) → State c → Return c
    go (𝔻 c) f (T,o & v & (P , P⊆) & t & p⊆ & s⊆ & ∃s@(Dₚ , Dₚ∈) & sechash & txout & part & val)
      with c
    -- Bd
    ... | withdraw A = λ where
      (here refl) →
       -, sig⋆ [ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
         { inputs  = [ T,o ]
         ; wit     = wit⊥
         ; relLock = [ 0 ]
         ; outputs = [ 1 , record { value = v ; validator = ƛ versig [ K {A} (p⊆ (here refl)) ] [ 0F ] } ]
         ; absLock = t }
    ... | A ∶ d
        = f (𝔻 d) ≺-auth (T,o & v & (P \\ [ A ] , P⊆ ∘ \\-⊆) & t & p⊆ ∘ there & s⊆ & ∃s & sechash & txout & part & val)
    ... | after t′ ∶ d
        = f (𝔻 d) ≺-after (T,o & v & (P , P⊆) & t ⊔ t′ & p⊆ & s⊆ & ∃s & sechash & txout & part & val)
    -- Bc
    ... | c′@(put zs &reveal as if p ⇒ cs) = λ where
      (here refl) → -, Tc
      (there x∈)  → f (C cs) ≺-put
        ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
        & p⊆ & s⊆ & tt
        & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
        & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆)
        x∈
       where
        n⊆ : names cs ⊆ names c′
        n⊆ = ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ʳ (map inj₁ as)

        cs⊆ : cs ⊆ subterms′ C₀′
        cs⊆ = s⊆ ∘ subterms⊆ᶜ

        zs⊆ : zs ⊆ namesʳ c′
        zs⊆ = (λ x∈ → ∈-mapMaybe⁺ isInj₂ x∈ refl) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

        k = length zs

        ins : Vec TxInput k
        ins rewrite sym (length-mapWith∈ (hashTxⁱ ∘ txout ∘ zs⊆))
                  = V.fromList (mapWith∈ zs (hashTxⁱ ∘ txout ∘ zs⊆))

        K⋆ : zs ↦ List KeyPair
        K⋆ = [_] ∘ K ∘ proj₂ ∘ part ∘ zs⊆

        wits : Vec (List KeyPair) k
        wits rewrite sym (length-mapWith∈ K⋆)
                   = V.fromList (mapWith∈ zs K⋆)

        Tc : Tx (suc k) 1
        Tc = sig⋆ (mapWith∈ P (K² Dₚ∈ ∘ P⊆) V.∷ wits) record
          { inputs  = T,o V.∷ ins
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ _ , record { value = v; validator = ƛ proj₂ (⋁ (mapWith∈ cs (Bout ∘ cs⊆))) } ]
          ; absLock = t }
        Tc♯ = (∃Tx ∋ -, -, Tc) ♯
    -- Bpar
    ... | c′@(split vcs) = λ where
      (here refl) → -, Tc
      (there x∈)  → f (VCS vcs) ≺-split
        ((Tc♯ at 0) & v & (partG , ⊆-refl) & 0
        & p⊆ & s⊆ & tt
        & sechash & txout & part & val)
        x∈
       where
        Tc : Txᶜ 1 c′
        Tc = sig⋆ [ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
          { inputs  = [ T,o ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.Mem.mapWith∈ (V.fromList vcs) λ{ {vᵢ , Cᵢ} x∈ →
              let eᵢ = mapWith∈ Cᵢ (Bout ∘ s⊆ ∘ subterms⊆ᵛ (V.Any.fromList⁻ x∈))
              in -, record { value = vᵢ ; validator = ƛ proj₂ (⋁ eᵢ) }
            }
          ; absLock = t }
        Tc♯ = (∃Tx ∋ -, -, Tc) ♯

    go (C x)  f st = ↦-∈  λ {d}  d∈  → f (𝔻 d)   (≺-∈ d∈)   (↓ st d∈)
      where
        ↓ : State (C ds) → ds ↦′ (State ∘ 𝔻)
        ↓ {ds = d ∷ ds} (T,o & v & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val) (here refl)
          = T,o & v & P⊆ & t & p⊆ ∘ ∈-++⁺ˡ & s⊆′ & (d , s⊆ (here refl))
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆
          where
            n⊆ : names d ⊆ names (d ∷ ds)
            n⊆ = ∈-++⁺ˡ

            s⊆′ : subterms′ (𝔻 d) ⊆ subterms′ C₀′
            s⊆′ = s⊆ ∘ there ∘ ∈-++⁺ˡ
        ↓ {ds = d ∷ ds} (T,o & v & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val) (there x∈)
          = ↓ {ds = ds} (T,o & v & P⊆ & t
          & p⊆ ∘ (∈-++⁺ʳ _) & s⊆ ∘ ∈-++⁺ʳ _ & tt
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part ∘ mapMaybe-⊆ isInj₂ n⊆ & val ∘ mapMaybe-⊆ isInj₂ n⊆) x∈
          where
            n⊆ : names ds ⊆ names (d ∷ ds)
            n⊆ = ∈-++⁺ʳ _
    go (VCS x) f st = ↦-∈ᵛ λ {cs} cs∈ → f (C cs) (≺-∈ᵛ cs∈) (↓ᵛ st cs∈)
      where
        ↓ᵛ : State (VCS vcs) → map proj₂ vcs ↦′ (State ∘ C)
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
