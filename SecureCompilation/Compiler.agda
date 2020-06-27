----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------

open import Induction
open import Induction.WellFounded

open import Data.Fin as Fin using (raise; inject+; toℕ)
import Data.Vec as V

open import Data.Nat using (_⊔_)
open import Data.Nat.Properties using (≤-refl; <-trans; n<1+n)

open import Data.List using (_++_; length; map; concat; sum; allFin; zip; take)
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.Setoid.Properties         using (length-mapWith∈)
open import Data.List.Relation.Unary.Any                   using (index)
open import Data.List.Relation.Unary.All                   using (lookup)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (⊆-refl)

open import Relation.Binary.PropositionalEquality using (setoid)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'

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
  (η : ℤ) -- public security nonce η, ensures adversaries cannot guess
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
        ; {-variables-} A; d; d′; ds; ds′; vcs )
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Contracts.Induction Participant Honest
open import BitML.Contracts.Validity Participant Honest

bitml-compiler :
    -- the input contract & precondition
    (ad : Advertisement)
    -- only compile valid advertisements
  → ValidAdvertisement ad
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (∀ {a} → inj₁ a ∈ names (G ad) → ℤ)
    -- txout: maps deposits in G to *pre-existing* transactions with the corresponding value
  → (∀ {d} → inj₂ d ∈ names (G ad) → TxInput)
    -- Exchanged keypairs K(A) and K(D,A)
  → (Participant → KeyPair)
  → (Contract → Participant → KeyPair)
    -- a set of transaction to be submitted
  → List ∃Tx
bitml-compiler (⟨ G₀ ⟩ C₀) (_ , names⊆ , putComponents⊆ , _) sechash txout K K²
  = Tinit
  ∷ concat (map-⊆ C₀ (⊆ᶜ-refl C₀) λ Dᵢ Dᵢ⊆C₀ →
      Bd Dᵢ (≺-wf (C Dᵢ)) Dᵢ⊆C₀ Dᵢ Tinit♯ 0 V partG 0)
  where
    partG : List Participant
    partG = nub (participants G₀)

    -- part: maps deposit names in G to the corresponding participant
    part : ∀ {x} → inj₂ x ∈ names G₀ → Participant
    part = proj₁ ∘ getDeposit {g = G₀}

    -- val: maps deposit names in G to the value contained in the deposit
    val : ∀ {x} → inj₂ x ∈ names G₀ → Value
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
                             in (hash bi `= ` (sechash (as⊆ a∈))) `∧ (` η `< Script.∣ bi ∣)))
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
            Bᵃʳ (Arith.∣ s ∣)  ⊆as = Script.∣ var (raise ς (index (⊆as (here refl)))) ∣ `- ` η
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

    Tinit : ∃Tx
    Tinit = _
          , _
          , record { inputs  = V.fromList (mapWith∈ (persistentDeposits G₀) (txout ∘ getName {g = G₀}))
                   ; wit     = wit⊥
                   ; relLock = V.replicate 0
                   ; outputs = V.[ _ , record { value     = V
                                              ; validator = ƛ (proj₂ (⋁ (map-⊆ C₀ (⊆ᶜ-refl C₀) Bout))) } ]
                   ; absLock = 0 }
    Tinit♯ = hashTx Tinit

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
