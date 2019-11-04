----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level    using (0ℓ)
open import Function using (const)

open import Data.Unit           using (⊤; tt)
open import Data.Product        using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Bool           using (Bool; true; false)
open import Data.Nat            using (ℕ; _+_; _>_; _≤_; _≤?_)
open import Data.Nat.Properties using (≰⇒≥)
open import Data.Fin as Fin     using (Fin; raise; inject+)
open import Data.Integer        using (ℤ; +_)
open import Data.List           using (List; []; _∷_; length; map; concatMap; foldr; sum; allFin; zip; upTo)
open import Data.Vec as V       using ()

open import Data.List.Relation.Unary.Any using (Any; here; there; index)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

-- Bitcoin
open import Bitcoin.BasicTypes
  using ($)
open import Bitcoin.Script.Base
  using ( ty; ScriptType; `Bool; `ℤ
        ; ctx; Ctx; ScriptContext
        ; var; `; _`+_; _`-_; _`=_; _`<_; `if_then_else_; hash; versig; absAfter_⇒_; relAfter_⇒_; Script
        ; _`∧_; `true; _`∨_; `false; `not
        ; ƛ_; BitcoinScript; ∃BitcoinScript
        ; ∣_∣
        )
open import Bitcoin.Tx.Base
  using ( TxInput
        ; ∃Tx
        )
open import Bitcoin.Tx.DecidableEquality
  using (module SETₜₓ; Set⟨Tx⟩)

module SecureCompilation.Compiler

  -- BitML parameters
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))

  -- Compilation parameters
  (η : ℤ) -- public security nonce η, ensures adversaries cannot guess
  where

-- BitML
open import BitML.BasicTypes Participant _≟ₚ_ Honest
  using ( Secret
        ; Time
        ; Value
        ; Values
        ; Iᵖ[_,_]
        ; ss; ss′; Predicate
        ; Arith
        )
open import BitML.Contracts.Types Participant _≟ₚ_ Honest
  using ( Iᶜ[_,_]
        ; ci; Contract; ∃Contract
        ; put_&reveal_if_⇒_∶-_; withdraw; split_∶-_; _∶_; after_∶_
        ; ∃Contracts
        ; ⟨_⟩_∶-_; ∃Advertisement
        ; participantsᵍ; toStipulate
        )
open import BitML.Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
  using (removeTopDecorations)

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

bitml-compiler : ∃Advertisement → Set⟨Tx⟩
bitml-compiler (_ , Iᵖ[ _ , vsᵖ ] , (⟨ G ⟩ C ∶- _))
  = SETₜₓ.fromList (Tinit ∷ concatMap compileChoice C)
  where
    postulate
      sechash : Secret → ℤ

    partG : List Participant
    partG = participantsᵍ G

    ς : ℕ
    ς = length partG

    V : Value
    V = sum vsᵖ -- (map proj₂ (toStipulate G))

    txout : Participant × Value → TxInput
    txout (p , vp) = record { txId  = {!!}
                            ; index = 0 }

    Bout : Contract ci → ∃[ ctx ] Script ctx `Bool
    Bout D with removeTopDecorations D
    ... | put zs &reveal as if p ⇒ C ∶- ss⊆
        = Ctx (ς + length as) , versig {!!} (map (inject+ (length as)) (allFin ς))
                             `∧ B p {-ss⊆ = proj₂ (proj₂ (ss⊆))-}
                             `∧ ⋀ (map (λ{ (i , a) → let bi = var (raise ς i) in
                                                      (hash bi `= ` (sechash a)) `∧ (` η `< ∣ bi ∣) })
                                   (zip (allFin (length as)) as))
          where
            Bᵃ : Arith ss → {-ss⊆ : ss ⊆ as →-} Script (Ctx (ς + length as)) `ℤ
            Bᵃ (Arith.` x)          = ` (+ x)
            Bᵃ (Arith.`len s) = let bi = var (raise ς {!!} {-(index (ss⊆ (here refl)))-})
                                      in ∣ bi ∣ `- ` η
            Bᵃ (x Arith.`+ y) = Bᵃ x `+ Bᵃ y
            Bᵃ (x Arith.`- y) = Bᵃ x `- Bᵃ y

            B : Predicate ss → {-ss⊆ : ss ⊆ as →-} Script (Ctx (ς + length as)) `Bool
            B Predicate.`True     = `true
            B (p Predicate.`∧ p′) = B p `∧ B p′
            B (Predicate.`¬ p)    = `not (B p)
            B (x Predicate.`≡ y)  = Bᵃ x `= Bᵃ y
            B (x Predicate.`< y)  = Bᵃ x `< Bᵃ y
    ... | _
        = _ , versig {!!} (allFin ς)

    Tinit : ∃Tx
    Tinit = _ , _ , record { inputs  = V.fromList (map txout (toStipulate G))
                           ; wit     = V.replicate (_ , V.[])
                           ; relLock = V.replicate 0
                           ; outputs = V.[ _ , record { value     = $ V
                                                      ; validator = ƛ (proj₂ (⋁ (map Bout C))) } ]
                           ; absLock = 0 }

    Bc : ∃Contracts
       → ∃Contract
       → ∃Tx
       → ℕ
       → Value
       → Values
       → List Participant
       → Time
       → List ∃Tx
    Bd : ∃Contract
       → ∃Contract
       → ∃Tx
       → ℕ
       → Value
       → List Participant
       → Time
       → List ∃Tx

    Bc C Dp T o v I P t = {!!}

    Bd (_ , (put zs &reveal as if p ⇒ C ∶- _)) Dp T o v P t = Bc (_ , C) Dp T o (v + {!!}) zs P t
    Bd (_ , (withdraw A)) Dp T o v P t = {!!}
    Bd (_ , (split cs ∶- _)) Dp T o v P t = {!!}
    Bd (_ , (A ∶ D′)) Dp T o v P t = {!!}
    Bd (_ , (after t′ ∶ D′)) Dp T o v P t = {!!}

    compileChoice : Contract ci → List ∃Tx
    compileChoice Di = Bd (_ , Di) (_ , Di) Tinit 0 V partG 0
