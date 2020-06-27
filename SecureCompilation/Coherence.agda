open import Function

open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Disjoint.Propositional
import Data.Vec as V

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Collections

open import Bitcoin.Crypto using (KeyPair)
open import BitML.BasicTypes

module SecureCompilation.Coherence
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℤ) -- security parameter
  where

open import BitML.Contracts.Helpers Participant Honest
open import SymbolicModel.Strategy Participant Honest as S

open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
open import Bitcoin.Crypto as C
open import Bitcoin.BasicTypes as C hiding (t)
open import Bitcoin.Script.Base as C hiding (`; ∣_∣)
open import Bitcoin.Tx.Base as C
open import Bitcoin.Tx.Crypto as C
open import Bitcoin.Consistency as C

Bitstring = ℤ

private
  variable
    ⟨G⟩C : Advertisement
    κ κ′ : Advertisement × Contract × Participant → KeyPair

-- !!! why is {{_}} necessary??
    txout′ : namesʳ {{HNʳ}} Rˢ ↦ TxInput
    txout : namesʳ {{HNʳ}} (Γₜ ∷⟦ α ⟧ Rˢ) ↦ TxInput
    sechash′ : namesˡ {{HNʳ}} Rˢ ↦ Bitstring
    sechash : namesˡ {{HNʳ}} (Γₜ ∷⟦ α ⟧ Rˢ) ↦ Bitstring

postulate
  encode : (namesʳ Rˢ ↦ TxInput) → Advertisement → Message
  -- ^ encode {G}C as a bitstring, representing each x in it as txout(x)

  infixr 4 _◇_
  _◇_ : Message → Message → Message

data coher₁ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  (txout′ : namesʳ Rˢ ↦ TxInput)
  (txout  : namesʳ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ TxInput)
  (sechash′ : namesˡ Rˢ ↦ Bitstring)
  (sechash  : namesˡ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ Bitstring)
  (κ′ κ : Advertisement × Contract × Participant → KeyPair)
  → Set
  where

  -- ** Advertising a contract
  [1] : ∀ {txout′ : namesʳ Rˢ ↦ TxInput} {sechash′ : namesˡ Rˢ ↦ Bitstring}

    → let
        Γ₀ , t = lastCfg Rˢ

        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        α  = advertise[ ⟨G⟩C ]
        Γ  = ` ⟨G⟩C ∣ Γ₀
        Γₜ = Γ at t
        λᶜ = A →∗∶ C

        namesʳ≡ : namesʳ Rˢ ≡ namesʳ (Γₜ ∷⟦ α ⟧ Rˢ)
        namesʳ≡ = ?

        namesˡ≡ : namesˡ Rˢ ≡ namesʳ (Γₜ ∷⟦ α ⟧ Rˢ)
        namesˡ≡ = ?

        txout : namesʳ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ TxInput
        txout = subst (_ ↦ TxInput) namesʳ≡ txout′

        sechash : namesˡ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ Bitstring
        sechash = subst (_ ↦ Bitstring) namesˡ≡ sechash′
      in

      --------------------------------------------------------
      coher₁ Rˢ a Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ′

  -- ** Stipulation: Committing Secrets
  [2] : ∀ {Δ×h̅ : List (Secret × Maybe ℕ × Bitstring)}
          {txout′ : namesʳ Rˢ ↦ TxInput}
          {sechash′ : namesˡ Rˢ ↦ Bitstring}

    → lastCfg Rˢ ≡ (` ⟨G⟩C ∣ Γ₀ at t)
    → let
        as : Secrets
        as = map proj₁ Δ×h̅

        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        Δ : List (Secret × Maybe ℕ)
        Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

        Δᶜ : Configuration
        Δᶜ = || map (λ{ (ai , Ni , _) → ⟨ A ∶ ai ♯ Ni ⟩}) Δ×h̅

        h̅ : List Bitstring -- ≈ Message
        h̅ = map (proj₂ ∘ proj₂) Δ×h̅

        k̅ : List KeyPair
        k̅ = ?

        -- T0D0: A should sign this
        C,h̅,k : Message
        C,h̅,k = C ◇ h̅ ◇ k̅

        α  = auth-commit[ A , ⟨G⟩C , Δ ]
        Γ  = ` ⟨G⟩C ∣ Γ₀ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
        Γₜ = Γ at t
        λᶜ = B →∗∶ C,h̅,k̅

        namesʳ≡ : namesʳ Rˢ ≡ namesʳ (Γₜ ∷⟦ α ⟧ Rˢ)
        namesʳ≡ = ?

        namesˡ↭ : namesˡ (Γₜ ∷⟦ α ⟧ Rˢ) ↭ namesˡ Rˢ ++ as
        namesˡ↭ = ?
      in

      -- (i) ⟨G⟩C has been previously advertised in Rᶜ
      -- T0D0: make sure it is the first occurrence of such a broadcast in Rᶜ
      ∃ λ B → (B →∗∶ C) ∈ Rᶜ

      -- (ii) broadcast message in Rᶜ
      -- T0D0: make sure that λᶜ is the first occurrence of such a message after C in Rᶜ
    -- → ∃ λ B → λᶜ ≡ B →∗∶ C,h̅,k̅
    → All (λ hᵢ → ∣ hᵢ ∣ ≡ η) Gh̅

      -- (iii) each hᵢ is obtained by querying the oracle, otherwise we have a dishonestly chosen secret
    → All (λ{ (_ , just Nᵢ , hᵢ) → ∃ λ B → ∃ λ mᵢ → ((B , mᵢ , hᵢ) ∈ oracleInteractions Rᶜ) × (∣ mᵢ ∣ ≡ η + Nᵢ)
            ; (_ , nothing , hᵢ) → hᵢ ∉ map (proj₂ ∘ proj₂)
                                            (filter ((η ≤?_) ∘ ∣_∣ ∘ proj₁ ∘ proj₂) (oracleInteractions Rᶜ))
            }) Δ×h̅

      -- (iv) no hash is reused
    → Unique h̅
    → Disjoint h̅ (codom sechash)

    → let
        -- (v) txout = txout′
        txout : namesʳ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ TxInput
        txout = subst (_ ↦ TxInput) namesʳ≡ txout′

        -- (vi) extend sechash′
        sechash : namesˡ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ Bitstring
        sechash = extend-↦ namesˡ↭ sechash′ (λ {aᵢ} aᵢ∈ → let hᵢ , _ = Any.lookup (∈-map⁻ proj₁ aᵢ∈) in hᵢ)

        -- (vii) extend κ′
        κ : Advertisement × Contract × Participant → KeyPair
        κ = ?
      in
      -----------------------------------------------------------------
      coher₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ


  -- ⋮


  -- [18] :

data coher₂
  (Rˢ : S.Run)
  (txout : namesʳ Rˢ ↦ TxInput)
  : C.Label
  → Set
  where

  [1] :

      Disjoint (V.toList (inputs (proj₂ (proj₂ T)))) (codom txout)
      -----------------------------------------------------------------
    → coher₂ Rˢ txout (submit T)

  [2] :

      (λᶜ ≡ A →O∶ m)
    ⊎ (λᶜ ≡ O→ A ∶ m)
      ------------------
    → coher₂ Rˢ txout λᶜ

  [3] :

    -- → where λᶜ does not correspond to any symbolic moves from coher₁
      -------------------------
      coher₂ Rˢ txout (A →∗∶ m)

data coher :
  (Rˢ : S.Run) (Rᶜ : C.Run)
  (txout : namesʳ Rˢ ↦ TxInput)
-- namesʳ Rˢ ↦ ∃(T , o). T ∈ trans Rᶜ
  (sechash : namesˡ Rˢ ↦ Bitstring)
  (κ : Advertisement × Contract × Participant → KeyPair)
-- Σ[ ⟨G⟩C ∈ Advertisement ] Σ[ c ∈ Contract ] c ∈ subterms (C ad)) × Participant → KeyPair
  → Set
  where

  base : ∀ {txout : namesʳ Rˢ ↦ TxInput} {sechash : namesˡ Rˢ ↦ Bitstring}

      -- (i) initial Rˢ
    → Rˢ ≡ (Γ₀ at 0) ∙
    → S.Initial Γ₀

      -- (ii) initial Rᶜ
    → C.Initial Rᶜ

      -- (iii) generation of public keys, we do not consider that here

      -- (iv) txout { ⟨ A , v ⟩ₓ ∈ Γ₀ ↦ T₀{value = $ v, spendable with K̂(A)(rₐ)} ∈ T₀ }
    -- → ?

      -- (v) dom sechash = ∅ , (vi) dom κ = ∅
    → names Rˢ ≡ []
      ---------------------------
    → coher Rˢ Rᶜ txout sechash κ


  step₁ : ∀ {txout′ : namesʳ Rˢ ↦ TxInput} {sechash′ : namesˡ Rˢ ↦ Bitstring}
            {txout : namesʳ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ TxInput} {sechash : namesˡ (Γₜ ∷⟦ α ⟧ Rˢ) ↦ Bitstring}

    → coher Rˢ Rᶜ txout′ sechash′ κ′
    → coher₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
      -------------------------------------------------------
    → coher (Γₜ ∷⟦ α ⟧ Rˢ) (Rᶜ ∷ʳ λᶜ) txout sechash κ

  step₂ : ∀ {txout : namesʳ Rˢ ↦ TxInput} {sechash : namesˡ Rˢ ↦ Bitstring}

    → coher Rˢ Rᶜ txout sechash κ
    → coher₂ Rˢ txout λᶜ
      -----------------------------------
    → coher Rˢ (Rᶜ ∷ʳ λᶜ) txout sechash κ

_~_ : S.Run → C.Run → Set
Rˢ ~ Rᶜ
  -- = ∃ (∃ (∃ (coher Rˢ Rᶜ)))
  = Σ[ txout ∈ (namesʳ Rˢ ↦ TxInput) ]
      Σ[ sechash ∈ (namesˡ Rˢ ↦ Bitstring) ]
        Σ[ κ ∈ (Advertisement × Contract × Participant → KeyPair) ]
          coher Rˢ Rᶜ txout sechash κ
