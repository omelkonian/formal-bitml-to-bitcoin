----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------

open import Function using (_∘_)

open import Data.Unit           using (⊤; tt)
open import Data.Product        using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum            using (inj₁; inj₂)
open import Data.Bool           using (Bool; true; false)
open import Data.Nat            using (ℕ; suc; _+_; _>_; _≤?_; _⊔_)
open import Data.Fin as Fin     using (Fin; raise; inject+; toℕ; 0F)
open import Data.Integer        using (ℤ; +_)
open import Data.List           using (List; []; _∷_; [_]; length; map; concat; sum; allFin; zip; take)
open import Data.Vec as V       using (Vec)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Membership.Setoid.Properties         using (length-mapWith∈)
open import Data.List.Relation.Unary.Any                   using (Any; here; there; index)
open import Data.List.Relation.Unary.All                   using (All; []; _∷_; lookup)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; inspect; setoid)
  renaming ([_] to ≡[_])

open import Prelude.Lists

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
        ; ∣_∣; ⋁; ⋀ )
open import Bitcoin.Tx.Base
  using ( _at_; TxInput
        ; Tx; ∃Tx
        ; Witness; ∃Witness )
open import Bitcoin.Tx.DecidableEquality
  using (module SETₜₓ; Set⟨Tx⟩)
open import Bitcoin.Tx.Crypto
  using (hashTx; sig⋆; wit⊥)

module SecureCompilation.Compiler

  -- BitML parameters
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))

  -- Compilation parameters
  (η : ℤ) -- public security nonce η, ensures adversaries cannot guess
  where

-- BitML
open import BitML.BasicTypes
  using ( Secret; Time; Value; Values; Id; Ids; Name; Names
        ; {-variables-} v; x; xs; as; t )
open import BitML.Predicate.Base
  using ( Predicate; Arith; secretsᵖʳ; secretsᵃʳ
        ; {-variables-} p )
open import BitML.Contracts.Types Participant _≟ₚ_ Honest
  using ( Contract; Contracts
        ; put_&reveal_if_⇒_; withdraw; split; _⇒_; after_⇒_
        ; Precondition
        ; ⟨_⟩_; Advertisement; G
        ; module SETₚ
        ; {-variables-} A; d; d′; ds; ds′; vcs )
open import BitML.Contracts.Helpers Participant _≟ₚ_ Honest
  using ( namesᵖ; secretsᵖ; participantsᵖ; depositsᵖ; persistentDepositsᵖ; removeTopDecorations
        ; namesᶜ; secretsᶜ; putComponentsᶜ
        ; namesᶜˢ; secretsᶜˢ; putComponentsᶜˢ
        ; namesᵛᶜˢ; secretsᵛᶜˢ; putComponentsᵛᶜˢ
        ; remove-names; remove-putComponents
        ; getDeposit; getName )
open import BitML.Contracts.Validity Participant _≟ₚ_ Honest
  using (ValidAdvertisement; _~_; _~′_; _~″_; _&_; map~; map~′; map~″; mapEnum~″)

--------------------------------------------

bitml-compiler :
    -- the input contract & precondition
    (ad : Advertisement)
    -- only compile valid advertisements
  → ValidAdvertisement ad
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (∀ {a} → inj₁ a ∈ namesᵖ (G ad) → ℤ)
    -- txout: maps deposits in G to *pre-existing* transactions with the corresponding value
  → (∀ {d} → inj₂ d ∈ namesᵖ (G ad) → TxInput)
    -- Exchanged keypairs K(A) and K(D,A)
  → (Participant → KeyPair)
  → (Contract → Participant → KeyPair)
    -- a set of transaction to be submitted
  → {-Set⟨Tx⟩-} List ∃Tx
{-# TERMINATING #-} -- due to interaction between Bc and Bd :(
bitml-compiler (⟨ G₀ ⟩ C₀) (_ , names⊆ , putComponents , _) sechash txout K K²
  = {-SETₜₓ.fromList-} (Tinit ∷ concat (map~ C₀ λ Dᵢ Dᵢ~C₀ → Bd (Dᵢ , Dᵢ~C₀) Dᵢ Tinit♯ 0 V partG 0))
  where
    partG : List Participant
    partG = SETₚ.nub (participantsᵖ G₀)

    -- part: maps deposit names in G to the corresponding participant
    part : ∀ {x} → inj₂ x ∈ namesᵖ G₀ → Participant
    part = proj₁ ∘ getDeposit {g = G₀}

    -- val: maps deposit names in G to the value contained in the deposit
    val : ∀ {x} → inj₂ x ∈ namesᵖ G₀ → Value
    val = proj₁ ∘ proj₂ ∘ getDeposit {g = G₀}

    -- K(D,ℙ): abbreviation for keys coming from multiple participant
    K⋆ : Contract → List Participant → List KeyPair
    K⋆ D = map (K² D)

    ς : ℕ
    ς = length partG

    V : Value
    V = sum (map (proj₁ ∘ proj₂) (persistentDepositsᵖ G₀))

    Bout : (d : Contract)
         → (d ~ C₀)
         → ∃[ ctx ] Script ctx `Bool
    Bout D (p⊆ & n⊆) with removeTopDecorations D | inspect removeTopDecorations D
    ... | put zs &reveal as if p ⇒ C | ≡[ eq ]
        = Ctx (ς + m) , ( versig (K⋆ D partG) (map (inject+ m) (allFin ς))
                     `∧ Bᵖʳ p p⊆as
                     `∧ ⋀ (mapEnumWith∈ as (λ i a a∈ →
                             let bi = var (raise ς i)
                             in (hash bi `= ` (sechash (as⊆ a∈))) `∧ (` η `< ∣ bi ∣)))
                        )

          where
            m : ℕ
            m = length as

            put∈ : (zs , as , p) ∈ putComponentsᶜ D
            put∈ rewrite remove-putComponents {D} | eq = here refl

            p⊆as : secretsᵖʳ p ⊆ as
            p⊆as = proj₂ (lookup putComponents (p⊆ put∈))

            as⊆ : ∀ {a} → a ∈ as → inj₁ a ∈ namesᵖ G₀
            as⊆ rewrite remove-names {D} | eq = names⊆ ∘ n⊆ ∘ ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₁

            Bᵃʳ : (e : Arith) → secretsᵃʳ e ⊆ as → Script (Ctx (ς + m)) `ℤ
            Bᵃʳ (Arith.` x)    _   = ` x
            Bᵃʳ (Arith.∣ s ∣)  ⊆as = ∣ var (raise ς (index (⊆as (here refl)))) ∣ `- ` η
            Bᵃʳ (x Arith.`+ y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `+ Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
            Bᵃʳ (x Arith.`- y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `- Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)

            Bᵖʳ : (e : Predicate) → secretsᵖʳ e ⊆ as → Script (Ctx (ς + m)) `Bool
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
          , record { inputs  = V.fromList (mapWith∈ (persistentDepositsᵖ G₀) (txout ∘ getName {g = G₀}))
                   ; wit     = wit⊥
                   ; relLock = V.replicate 0
                   ; outputs = V.[ _ , record { value     = V
                                              ; validator = ƛ (proj₂ (⋁ (map~ C₀ Bout))) } ]
                   ; absLock = 0 }
    Tinit♯ = hashTx Tinit

    Bc : Σ[ C ∈ Contracts ] C ~′ C₀
       → Contract
       → HashId
       → ℕ
       → Value
       → Σ[ I ∈ Ids ] (∀ {i} → i ∈ I → inj₂ i ∈ namesᵖ G₀)
       → List Participant
       → Time
       → List ∃Tx

    Bd : Σ[ D ∈ Contract ] D ~ C₀
       → Contract
       → HashId
       → ℕ
       → Value
       → List Participant
       → Time
       → List ∃Tx

    Bpar : Σ[ vcs ∈ List (Value × Contracts) ] vcs ~″ C₀
         → Contract
         → HashId
         → ℕ
         → List Participant
         → Time
         → List ∃Tx

    Bd (put zs &reveal as if _ ⇒ C , p⊆ & n⊆) Dp T o v P t
      = Bc (C , C~C₀) Dp T o (v + sum (mapWith∈ zs (val ∘ zs⊆))) zs′ P t
          where
            C~C₀ : C ~′ C₀
            C~C₀ = (p⊆ ∘ ∈-++⁺ʳ _) & (n⊆ ∘ ∈-++⁺ʳ (map inj₂ zs) ∘ ∈-++⁺ʳ (map inj₁ as))

            zs′ : Σ[ I ∈ Ids ] (∀ {i} → i ∈ I → inj₂ i ∈ namesᵖ G₀)
            zs′ = zs , λ z∈ → names⊆ (n⊆ (∈-++⁺ˡ (∈-map⁺ inj₂ z∈)))

            zs⊆ : ∀ {z} → z ∈ zs → inj₂ z ∈ namesᵖ G₀
            zs⊆ = names⊆ ∘ n⊆ ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

    Bd (withdraw A , D~C₀) Dp T o v P t
      = [ _
        , _
        , sig⋆ V.[ K⋆ Dp P ]
               (record { inputs  = V.[ T at 0 ]
                       ; wit     = wit⊥
                       ; relLock = V.[ 0 ]
                       ; outputs = V.[ Ctx 1 , record { value = v ; validator = ƛ (versig [ K A ] [ 0F ]) } ]
                       ; absLock = t })
        ]
    Bd (split Cs , p⊆ & n⊆) Dp T o v P t
      with sum (map proj₁ Cs) ≤? v
    ... | no  _ = []
    ... | yes _ = Bpar (Cs , p⊆ & n⊆) Dp T o P t
    Bd (A ⇒ D′ , p⊆ & n⊆) Dp T o v P t
      = Bd (D′ , p⊆ & n⊆) Dp T o v (P SETₚ.\\ [ A ]) t
    Bd (after t′ ⇒ D′ , p⊆ & n⊆) Dp T o v P t
      = Bd (D′ , p⊆ & n⊆) Dp T o v P (t ⊔ t′)

    Bc (C , C~C₀) Dp T o v (I , I⊆) P t = Tc ∷ concat (map~′ C C~C₀ λ Dᵢ Dᵢ~C₀ → Bd (Dᵢ , Dᵢ~C₀) Dᵢ Tc♯ 0 v partG t)
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
           , sig⋆ (K⋆ Dp P V.∷ wits)
                  (record { inputs  = T at o V.∷ ins
                          ; wit     = wit⊥
                          ; relLock = V.replicate 0
                          ; outputs = V.[ _ , record { value     = v
                                                     ; validator = ƛ (proj₂ (⋁ (map~′ C C~C₀ Bout))) } ]
                          ; absLock = t })
        Tc♯ = hashTx Tc

    Bpar (vcs , vcs~C₀) Dp T o P t
      = Tc ∷ Tᵢⱼ
      where
        eᵢⱼ : List (Value × List (∃[ ctx ] Script ctx `Bool))
        eᵢⱼ = map~″ vcs vcs~C₀ λ v Cᵢ Cᵢ~C₀ →
                v , map~′ Cᵢ Cᵢ~C₀ Bout

        Tc : ∃Tx
        Tc = _
           , _
           , sig⋆ V.[ K⋆ Dp P ]
                  (record { inputs  = V.[ T at o ]
                          ; wit     = wit⊥
                          ; relLock = V.replicate 0
                          ; outputs = V.map (λ{ (vᵢ , eᵢ) → _ , record { value     = vᵢ
                                                                       ; validator = ƛ (proj₂ (⋁ eᵢ)) }})
                                            (V.fromList eᵢⱼ)
                          ; absLock = t })
        Tc♯ = hashTx Tc

        Tᵢⱼ : List ∃Tx
        Tᵢⱼ = concat (mapEnum~″ vcs vcs~C₀ λ i vᵢ Cᵢ Cᵢ~C₀ →
                concat (map~′ Cᵢ Cᵢ~C₀ λ Dᵢⱼ Dᵢⱼ~C₀ →
                  Bd (Dᵢⱼ , Dᵢⱼ~C₀) Dᵢⱼ Tc♯ (toℕ i) vᵢ partG 0))
