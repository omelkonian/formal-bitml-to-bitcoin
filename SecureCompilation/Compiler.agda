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
open import Data.Fin as Fin     using (Fin; raise; inject+; 0F)
open import Data.Integer        using (ℤ; +_)
open import Data.List           using (List; []; _∷_; length; map; concatMap; foldr; sum; allFin; zip; upTo; _++_)
open import Data.Vec as V       using (Vec)

open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Any                   using (Any; here; there; index)
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
  using (Secret; Time; Value; Values)
open import BitML.Predicate.Base as Pred
  using (Predicate)
open import BitML.Contracts.Types Participant _≟ₚ_ Honest
  using ( Iᵖ[_,_]; Iᶜ[_,_]
        ; ci; Contract; ∃Contract
        ; ContractCases
        ; put_&reveal_if_⇒_∶-_; withdraw; split_∶-_; _∶_; after_∶_
        ; ∃Contracts
        ; ⟨_⟩_∶-_; ∃Advertisement
        ; participantsᵍ; toStipulate
        ; module SETₚ
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
{-# NON_TERMINATING #-} -- due to interaction between Bc and Bd :(
bitml-compiler (_ , Iᵖ[ _ , vsᵖ ] , (⟨ G ⟩ C ∶- _))
  = SETₜₓ.fromList (Tinit ∷ concatMap compileChoice C)
  where
    postulate
      -- maps secrets in G to the corresponding committed hashes
      sechash : Secret → ℤ
      -- maps deposits in G to *pre-existing* transactions with the corresponding value
      txout   : ∀ {d} → d ∈ toStipulate G → Tx 0 1

    txout′ : ∀ {d} → d ∈ toStipulate G → TxInput
    txout′ = _at 0 ∘ hashTx ∘ txout

    partG : List Participant
    partG = participantsᵍ G

    ς : ℕ
    ς = length partG

    V : Value
    V = sum vsᵖ -- (map proj₂ (toStipulate G))

    Bout : Contract ci → ∃[ ctx ] Script ctx `Bool
    Bout D with removeTopDecorations D
    ... | put_&reveal_if_⇒_∶-_ {n = n} zs as p C _
        = Ctx (ς + n) , ( versig {!!} (map (inject+ n) (allFin ς))
                       `∧ B p
                       `∧ ⋀ (map (λ{ (i , a) → let bi = var (raise ς i) in
                                               (hash bi `= ` (sechash a)) `∧ (` η `< ∣ bi ∣) })
                                 (zip (allFin n) (V.toList as)))
                        )
          where

            Bᵗʸ : Pred.ExpressionType → ScriptType
            Bᵗʸ Pred.`Bool = `Bool
            Bᵗʸ Pred.`ℤ    = `ℤ

            B : Pred.Expression (Pred.Ctx n) Pred.ty → Script (Ctx (ς + n)) (Bᵗʸ Pred.ty)
            B (Pred.∣ s ∣)   = ∣ var (raise ς s) ∣ `- ` η
            B (Pred.` x)     = ` x
            B (x Pred.`+ y)  = B x `+ B y
            B (x Pred.`- y)  = B x `- B y
            B (x Pred.`= y)  = B x `= B y
            B (x Pred.`< y)  = B x `< B y
            B Pred.`true     = `true
            B (p Pred.`∧ p′) = B p `∧ B p′
            B (Pred.`¬ p)    = `not (B p)
    ... | _
        = _ , versig {!!} (allFin ς)

    Tinit : ∃Tx
    Tinit = _ , _ , record { inputs  = V.fromList (mapWith∈ (toStipulate G) txout′)
                           ; wit     = V.replicate (_ , V.[])
                           ; relLock = V.replicate 0
                           ; outputs = V.[ _ , record { value     = V
                                                      ; validator = ƛ (proj₂ (⋁ (map Bout C))) } ]
                           ; absLock = 0 }
    Tinit♯ = hashTx (proj₂ (proj₂ Tinit))

    Bc : ∃Contracts
       → ∃Contract
       → HashId
       → ℕ
       → Value
       → Values
       → List Participant
       → Time
       → List ∃Tx

    Bd : ∃Contract
       → ∃Contract
       → HashId
       → ℕ
       → Value
       → List Participant
       → Time
       → List ∃Tx
    Bpar : ∃[ vs ] (ContractCases vs)
         → ∃Contract
         → HashId
         → ℕ
         → List Participant
         → Time
         → List ∃Tx


    Bd (_ , (put zs &reveal _ if _ ⇒ C ∶- _)) Dp T o v P t
      = Bc (_ , C) Dp T o (v + sum zs) zs P t

    Bd (_ , (withdraw A)) Dp T o v P t
      = [ _ , _ , record { inputs  = V.[ T at 0 ]
                         ; wit     = V.[ _ , V.[ sig {!!} {!!} {!!} ] ]
                         ; relLock = V.[ 0 ]
                         ; outputs = V.[ _ , record { value = v ; validator = ƛ (versig {!!} (allFin _)) } ]
                         ; absLock = t } ]
    Bd (_ , (split Cs ∶- _)) Dp T o v P t
      = Bpar (_ , Cs) Dp T o P t
    Bd (_ , (A ∶ D′)) Dp T o v P t
      = Bd (_ , D′) Dp T o v (P SETₚ.\\ [ A ]) t
    Bd (_ , (after t′ ∶ D′)) Dp T o v P t
      = Bd (_ , D′) Dp T o v P (t ⊔ t′)

    compileChoice : Contract ci → List ∃Tx
    compileChoice Di = Bd (_ , Di) (_ , Di) Tinit♯ 0 V partG 0

    Bc (_ , C) Dp T o v I P t = Tc ∷ concatMap compileChoice′ C
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
                                                ; validator = ƛ (proj₂ (⋁ (map Bout C))) }) ]
                    ; absLock = t }
        Tc♯ = hashTx (proj₂ (proj₂ Tc))

        compileChoice′ : Contract ci → List ∃Tx
        compileChoice′ Di = Bd (_ , Di) (_ , Di) Tc♯ 0 v partG t

    Bpar (vs , Cs) Dp T o P t = Tc ∷ concatMap compileCases Cs
      where
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
                                                      ; validator = ƛ (proj₂ (⋁ (map Bout Ci))) })
                                      (V.fromList (upTo n))
                    ; absLock = t }
        Tc♯ = hashTx (proj₂ (proj₂ Tc))

        compileCases : ∃[ v ] Contract Iᶜ[ v , vs ] → List ∃Tx
        compileCases (_ , Di) = Bd (_ , Di) (_ , Di) Tc♯ {!!} {- i - 1 -} {!!} {- vs ‼ i -} partG 0
