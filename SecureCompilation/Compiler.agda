----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------
-- {-# OPTIONS --allow-unsolved-metas #-}

open import Level    using (0ℓ)
open import Function using (_∘_; case_of_)

open import Data.Unit           using (⊤; tt)
open import Data.Product        using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Bool           using (Bool; true; false)
open import Data.Nat            using (ℕ; suc; _+_; _>_; _≤_; _≤?_; _⊔_)
open import Data.Nat.Properties using (≰⇒≥)
open import Data.Fin as Fin     using (Fin; raise; inject+; 0F; toℕ)
open import Data.Integer        using (ℤ; +_)
open import Data.List           using ( List; []; _∷_; [_]; length; map; concatMap; foldr
                                      ; sum; allFin; zip; upTo; _++_; take
                                      )
open import Data.Vec as V       using (Vec)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Membership.Propositional.Properties  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any                   using (Any; here; there; index)
open import Data.List.Relation.Unary.All                   using (All; []; _∷_; lookup)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

-- Bitcoin
open import Bitcoin.BasicTypes
  using (HashId)
open import Bitcoin.Script.Base
  using ( ty; ScriptType; `Bool; `ℤ
        ; ctx; Ctx; ScriptContext
        ; var; `; _`+_; _`-_; _`=_; _`<_; `if_then_else_; hash; versig; absAfter_⇒_; relAfter_⇒_; Script
        ; _`∧_; `true; _`∨_; `false; `not
        ; ƛ_; BitcoinScript; ∃BitcoinScript
        ; ∣_∣
        )
open import Bitcoin.Tx.Base
  using ( _at_; TxInput
        ; Tx; ∃Tx
        )
open import Bitcoin.Tx.DecidableEquality
  using (module SETₜₓ; Set⟨Tx⟩)
open import Bitcoin.Tx.Crypto
  using (hashTx; sig)

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
  using (Secret; Time; Value; Values; Id; Ids)
open import BitML.Predicate.Base
  using (Predicate; Arith; secretsᵖʳ; secretsᵃʳ)
open import BitML.Contracts.Types Participant _≟ₚ_ Honest
  using ( Contract; Contracts
        ; put_&reveal_if_⇒_; withdraw; split; _⇒_; after_⇒_
        ; ⟨_⟩_; Advertisement; G
        ; module SETₚ
        )
open import BitML.Contracts.Helpers Participant _≟ₚ_ Honest
  using ( allSecretsᵖ; participantsᵖ; depositsᵖ; persistentDepositsᵖ; removeTopDecorations
        ; putComponentsᶜ; putComponentsᶜˢ
        )
open import BitML.Contracts.Validity Participant _≟ₚ_ Honest
  using (ValidAdvertisement)

--------------------------------------------

mapFin : ∀ {n m} → (Fin n → Fin m) → Script (Ctx n) ty → Script (Ctx m) ty
mapFin f (var x)                 = var (f x)
mapFin f (` x)                   = ` x
mapFin f (s `+ s₁)               = mapFin f s `+ mapFin f s₁
mapFin f (s `- s₁)               = mapFin f s `- mapFin f s₁
mapFin f (s `= s₁)               = mapFin f s `= mapFin f s₁
mapFin f (s `< s₁)               = mapFin f s `< mapFin f s₁
mapFin f (`if s then s₁ else s₂) = `if mapFin f s then mapFin f s₁ else mapFin f s₂
mapFin f ∣ s ∣                   = ∣ mapFin f s ∣
mapFin f (hash s)                = hash (mapFin f s)
mapFin f (versig x x₁)           = versig x (map f x₁)
mapFin f (absAfter x ⇒ s)        = absAfter x ⇒ mapFin f s
mapFin f (relAfter x ⇒ s)        = relAfter x ⇒ mapFin f s

inject≤ : ∀ {m n} → .(n ≤ m) → Fin n → Fin m
inject≤ m≤n fn = Fin.inject≤ fn m≤n

⋁ : List (∃[ ctx ] Script ctx `Bool) → ∃[ ctx′ ] Script ctx′ `Bool
⋁ [] = Ctx 0 , `false
⋁ ((Ctx n , x) ∷ xs) with ⋁ xs
... | Ctx m , y      with n ≤? m
... | yes n≤m      = Ctx m , (mapFin (inject≤ n≤m) x `∨ y)
... | no  n≰m      = Ctx n , (x `∨ mapFin (inject≤ (≰⇒≥ n≰m)) y)

⋀ : List (Script ctx `Bool) → Script ctx `Bool
⋀ = foldr _`∧_ `true

-- names→secrets : ∀ {c : Contract} {g : Precondition}
--   → namesᶜ c ⊆ namesᵖ g
--   → secretsᶜ ⊆ allSecretsᵖ g

bitml-compiler :
    -- the input contract & precondition
    (ad : Advertisement)
    -- only compile valid advertisements
  → ValidAdvertisement ad
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (∀ {a} → a ∈ allSecretsᵖ (G ad) → ℤ)
    -- txout: maps deposits in G to *pre-existing* transactions with the corresponding value
  → (∀ {d} → d ∈ persistentDepositsᵖ (G ad) → ∃[ i ] ∃[ o ] (Tx i o × Fin o))
    -- val: maps deposit names in G to the value contained in the deposit
  → (∀ {x} → x ∈ depositsᵖ (G ad) → Value)
    -- a set of transaction to be submitted
  → Set⟨Tx⟩
{-# NON_TERMINATING #-} -- due to interaction between Bc and Bd :(
bitml-compiler (⟨ G ⟩ C) (uniqNames , names⊆ , putComponents , parts⊆) sechash txout val
  = SETₜₓ.fromList (Tinit ∷ concatMap compileChoice C)
  where
    txout′ : ∀ {d} → d ∈ persistentDepositsᵖ G → TxInput
    txout′ d∈ with txout d∈
    ... | (_ , _ , tx , o) = hashTx tx at toℕ o

    partG : List Participant
    partG = participantsᵖ G

    ς : ℕ
    ς = length partG

    V : Value
    V = sum (map (proj₁ ∘ proj₂) (persistentDepositsᵖ G))

    Bout : (c : Contract)
         → (putComponentsᶜ c ⊆ putComponentsᶜˢ C)
         × (secretsᶜ c ⊆ allSecretsᵖ G)
         → ∃[ ctx ] Script ctx `Bool
    Bout D (put⊆ , secrets⊆) with removeTopDecorations D
    ... | put zs &reveal as if p ⇒ C
        = Ctx (ς + m) , ( versig {!!} (take ς (allFin (ς + m)))
                     `∧ B p p⊆as
                     `∧ ⋀ (mapEnumWith∈ as (λ i a a∈ →
                             let bi = var (raise ς i)
                             in (hash bi `= ` (sechash {a} (as⊆ a∈))) `∧ (` η `< ∣ bi ∣)))
                        )

          where
            m : ℕ
            m = length as

            put∈ : (zs , as , p) ∈ putComponentsᶜ D
            put∈ = {!here refl!}

            as⊆ : as ⊆ allSecretsᵖ G
            as⊆ = {!names⊆!}

            p⊆as : secretsᵖʳ p ⊆ as
            p⊆as = proj₂ (lookup putComponents (put⊆ put∈))

            Bᵃʳ : (e : Arith) → secretsᵃʳ e ⊆ as → Script (Ctx (ς + m)) `ℤ
            Bᵃʳ (Arith.` x)    _   = ` x
            Bᵃʳ (Arith.∣ s ∣)  ⊆as = ∣ var (raise ς (index (⊆as (here refl)))) ∣ `- ` η
            Bᵃʳ (x Arith.`+ y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `+ Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
            Bᵃʳ (x Arith.`- y) ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `- Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)

            B : (e : Predicate) → secretsᵖʳ e ⊆ as → Script (Ctx (ς + m)) `Bool
            B Predicate.`true     _   = `true
            B (p Predicate.`∧ p′) ⊆as = B p (⊆as ∘ ∈-++⁺ˡ) `∧ B p′ (⊆as ∘ ∈-++⁺ʳ _)
            B (Predicate.`¬ p)    ⊆as = `not (B p ⊆as)
            B (x Predicate.`= y)  ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `= Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
            B (x Predicate.`< y)  ⊆as = Bᵃʳ x (⊆as ∘ ∈-++⁺ˡ) `< Bᵃʳ y (⊆as ∘ ∈-++⁺ʳ _)
    ... | _
        = _ , versig {!!} (allFin ς)

    Tinit : ∃Tx
    Tinit = _ , _ , record { inputs  = V.fromList (mapWith∈ (persistentDepositsᵖ G) txout′)
                           ; wit     = V.replicate (_ , V.[])
                           ; relLock = V.replicate 0
                           ; outputs = V.[ _ , record { value     = V
                                                      ; validator = ƛ (proj₂ (⋁ (map (λ c → Bout c {!!}) C))) } ]
                           ; absLock = 0 }
    Tinit♯ = hashTx (proj₂ (proj₂ Tinit))

    Bc : Contracts
       → Contract
       → HashId
       → ℕ
       → Value
       → Ids
       → List Participant
       → Time
       → List ∃Tx

    Bd : Contract
       → Contract
       → HashId
       → ℕ
       → Value
       → List Participant
       → Time
       → List ∃Tx
    Bpar : List (Value × Contracts)
         → Contract
         → HashId
         → ℕ
         → List Participant
         → Time
         → List ∃Tx


    Bd (put zs &reveal _ if _ ⇒ C ) Dp T o v P t
      = Bc C Dp T o (v + sum (map val {!!} {-zs-})) zs P t

    Bd (withdraw A) Dp T o v P t
      = [ _ , _ , record { inputs  = V.[ T at 0 ]
                         ; wit     = V.[ _ , V.[ sig {!!} {!!} {!!} ] ]
                         ; relLock = V.[ 0 ]
                         ; outputs = V.[ _ , record { value = v ; validator = ƛ (versig {!!} (allFin _)) } ]
                         ; absLock = t } ]
    Bd (split Cs) Dp T o v P t
      = Bpar Cs Dp T o P t
    Bd (A ⇒ D′) Dp T o v P t
      = Bd D′ Dp T o v (P SETₚ.\\ [ A ]) t
    Bd (after t′ ⇒ D′) Dp T o v P t
      = Bd D′ Dp T o v P (t ⊔ t′)

    compileChoice : Contract → List ∃Tx
    compileChoice Di = Bd Di Di Tinit♯ 0 V partG 0

    Bc C Dp T o v I P t = Tc ∷ concatMap compileChoice′ C
      where
        postulate
          i  : ℕ
          I′ : Vec Value i

        Tc : ∃Tx
        Tc = suc i
           , _
           , record { inputs  = T at o
                            V.∷ V.map (txout′ ∘ {!!}) I′
                    ; wit     = (_ , V.[ sig {!!} {!!} {!!} ])
                            V.∷ V.map (λ v′ → _ , V.[ sig {!!} {!!} {!!} ]) I′
                    ; relLock = V.replicate 0
                    ; outputs = V.[ _ , (record { value     = v
                                                ; validator = ƛ (proj₂ (⋁ (map (λ c → Bout c {!!}) C))) }) ]
                    ; absLock = t }
        Tc♯ = hashTx (proj₂ (proj₂ Tc))

        compileChoice′ : Contract → List ∃Tx
        compileChoice′ Di = Bd Di Di Tc♯ 0 v partG t

    Bpar vcs Dp T o P t = Tc ∷ concatMap compileCases Cs
      where
        Cs : List Contracts
        Cs = map proj₂ vcs

        n = length Cs

        Tc : ∃Tx
        Tc = _
           , _
           , record { inputs  = V.[ T at o ]
                    ; wit     = V.[ _ , V.[ sig {!!} {!!} {!!} ] ]
                    ; relLock = V.replicate 0
                    ; outputs = V.map (λ _ →
                                        let Ci = {!!} {- Cs ‼ i -}
                                            vi = {!!} {- vs ‼ i -}
                                        in _ , record { value     = vi
                                                      ; validator = ƛ (proj₂ (⋁ (map (λ c → Bout c {!!}) Ci))) })
                                      (V.fromList (upTo n))
                    ; absLock = t }
        Tc♯ = hashTx (proj₂ (proj₂ Tc))

        compileCases : Contracts → List ∃Tx
        compileCases = concatMap go
          where
            go : Contract → List ∃Tx
            go Di = Bd Di Di Tc♯ {!!} {- i - 1 -} {!!} {- vs ‼ i -} partG 0
