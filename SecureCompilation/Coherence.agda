open import Data.List.Membership.Propositional.Properties

open import Prelude.Init hiding (T)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Collections
open import Prelude.Monoid

open import Bitcoin.Crypto using (KeyPair)
open import BitML.BasicTypes renaming (Value to Val)

module SecureCompilation.Coherence
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import BitML.Contracts.Helpers Participant Honest
open import BitML.Contracts.Validity Participant Honest
open import SymbolicModel.Strategy Participant Honest as S

open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
open import Bitcoin.Crypto as C
open import Bitcoin.BasicTypes as C hiding (t)
open import Bitcoin.Script.Base as C hiding (`; ∣_∣)
open import Bitcoin.Tx.Base as C
open import Bitcoin.Tx.Crypto as C
open import Bitcoin.Consistency as C

open import SecureCompilation.Compiler Participant Honest η

postulate
  encode : (namesʳ Rˢ ↦ TxInput) → Advertisement → Message
  -- ^ encode {G}C as a bitstring, representing each x in it as txout(x)

  SIGᵖ : ∀ {A : Set} → ℤ {- public key -} → A → ℤ

  ∣_∣ᶻ : ℤ → ℕ
  ∣_∣ᵐ : Message → ℕ

  ads : S.Run → List Advertisement

  subtermsᵈ : Contracts → List Contract
  subtermsᶜ : Contracts → List Contracts

  ancestor : (c : Contracts) → Val × Id → Configuration → ∃[ ad ] (c ∈ subtermsᶜ (C ad))

  labels : S.Run → List S.Label

_-redeemableWith-_ : Val → KeyPair → ∃TxOutput
v -redeemableWith- k = Ctx 1 , record {value = v;  validator = ƛ (versig [ k ] [ # 0 ])}

-- T0D0: redefine Message ≈ ℤ ??
SIGᵐ : KeyPair → Message → Message
SIGᵐ k = map (SIG k)

_↑_ : ∀ {A : Set} {P : A → Set} {xs xs′ : List A} → xs ↦′ P → xs′ ≡ xs → xs′ ↦′ P
f ↑ refl = f

cons-↦ : ∀ {A : Set} {P : A → Set} {xs xs′ : List A}
  → (x : A)
  → P x
  → xs ↦′ P
  → (x ∷ xs) ↦′ P
cons-↦ _ y _ (here refl) = y
cons-↦ _ _ f (there x∈)  = f x∈

Txout Sechash : S.Run → Set
Txout   Rˢ = namesʳ Rˢ ↦ TxInput
Sechash Rˢ = namesˡ Rˢ ↦ ℤ

Κ′ : Advertisement → Set
Κ′ (⟨ G ⟩ C) = subtermsᵈ C ↦ (participants G ↦ ℤ)

Κ : Set
Κ = ∃ (_↦′ Κ′)

_∷ᵏ_∶-_ : (ad : Advertisement) → Κ → Κ′ ad → Κ
ad ∷ᵏ (ads , f) ∶- g = (ad ∷ ads) , f′
  where
    f′ : ∀[ ⟨G⟩C ∈ (ad ∷ ads) ] (subtermsᵈ (C ⟨G⟩C) ↦ (participants (G ⟨G⟩C) ↦ ℤ))
    f′ (here refl) = g
    f′ (there ad∈) = f ad∈


private
  variable
    κ κ′ : Κ
--   Rˢ       : S.Run
--   txout′   : Txout Rˢ
--   txout    : Txout (Γₜ ∷⟦ α ⟧ Rˢ)
--   sechash′ : Sechash Rˢ
--   sechash  : Sechash (Γₜ ∷⟦ α ⟧ Rˢ)

    ⟨G⟩C : Advertisement
    T T′ : ∃Tx

-- ** Types and notation.
data coher : (Rˢ : S.Run) (Rᶜ : C.Run) (txout : Txout Rˢ) (sechash : Sechash Rˢ) (κ : Κ) → Set
data coher₂ (Rˢ : S.Run) (txout : Txout Rˢ) : C.Label → Set
data coher₁ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  (txout′ : Txout Rˢ) (txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ))
  (sechash′ : Sechash Rˢ) (sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ))
  (κ′ : Κ) (κ : Κ)
  → Set
data coher₁₁ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  (txout′ : Txout Rˢ) (txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ))
  (sechash′ : Sechash Rˢ) (sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ))
  (κ′ : Κ) (κ : Κ)
  → Set
data coher₁₂ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  (txout′ : Txout Rˢ) (txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ))
  (sechash′ : Sechash Rˢ) (sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ))
  (κ′ : Κ) (κ : Κ)
  → Set

-- ** Definitions.
data coher₁ where
  [L] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
               {txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ)} {sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ)}
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
    → coher₁  Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

  [R] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
               {txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ)} {sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ)}
    → coher₁₂ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
    → coher₁  Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

data coher₁₁ where

  -- ** Advertising a contract
  [1] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → let
        Γ₀ at t = lastCfg Rˢ

        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        α  = advertise[ ⟨G⟩C ]
        Γ  = ` ⟨G⟩C ∣ Γ₀
        Γₜ = Γ at t
        λᶜ = A →∗∶ C
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in
      --------------------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ κ

  -- ** Stipulation: committing Secrets
  [2] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
          {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
          {k⃗ : subtermsᵈ (C ⟨G⟩C) ↦ (participants (G ⟨G⟩C) ↦ ℤ)}

    → lastCfg Rˢ ≡ (` ⟨G⟩C ∣ Γ₀ at t)
    → let
        as : Secrets
        as = map proj₁ Δ×h̅

        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        Δ : List (Secret × Maybe ℕ)
        Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

        Δᶜ : Configuration
        Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ

        h̅ : List ℤ -- ≈ Message
        h̅ = map (proj₂ ∘ proj₂) Δ×h̅

        k̅ : List ℤ -- ≈ Message
        k̅ = concatMap codom (codom k⃗)

        C,h̅,k̅ : Message
        C,h̅,k̅ = C ◇ h̅ ◇ k̅

        C,h̅,k̅ₐ : Message
        C,h̅,k̅ₐ = SIGᵐ (K A) C,h̅,k̅

        α  = auth-commit[ A , ⟨G⟩C , Δ ]
        Γ  = ` ⟨G⟩C ∣ Γ₀ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
        Γₜ = Γ at t
        λᶜ = B →∗∶ C,h̅,k̅ₐ
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ↭ : namesˡ Rˢ′ ↭ namesˡ Rˢ ++ as
        namesˡ↭ = {!!}

        -- (v) txout = txout′
        txout : Txout Rˢ′
        txout = txout′ ↑ namesʳ≡

        -- -- (vi) extend sechash′
        sechash : Sechash Rˢ′
        sechash = extend-↦ namesˡ↭ sechash′ (proj₂ ∘ proj₂ ∘ proj₁ ∘ ∈-map⁻ proj₁)

        -- (vii) extend κ′
        κ : Κ
        κ =
          if ⌊ A ∉? S.Hon ⌋ ∨ ⌊ ⟨G⟩C ∈? proj₁ κ′ ⌋ then
            κ′
          else
            ⟨G⟩C ∷ᵏ κ′ ∶- k⃗
      in

      -- (i) ⟨G⟩C has been previously advertised in Rᶜ
      -- T0D0: make sure it is the first occurrence of such a broadcast in Rᶜ
      (∃ λ B → (B →∗∶ C) ∈ Rᶜ)

      -- (ii) broadcast message in Rᶜ
      -- T0D0: make sure that λᶜ is the first occurrence of such a message after C in Rᶜ
    -- → ∃ λ B → λᶜ ≡ B →∗∶ C,h̅,k̅ₐ
    → All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅

      -- (iii) each hᵢ is obtained by querying the oracle, otherwise we have a dishonestly chosen secret
    → All (λ{ (_ , just Nᵢ , hᵢ)
            → ∃ λ B → ∃ λ mᵢ → ((B , mᵢ , [ hᵢ ]) ∈ oracleInteractions Rᶜ) × (∣ mᵢ ∣ᵐ ≡ η + Nᵢ)
            ; (_ , nothing , hᵢ)
            → [ hᵢ ] ∉ map (proj₂ ∘ proj₂) (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ proj₁ ∘ proj₂) (oracleInteractions Rᶜ))
            }) Δ×h̅

      -- (iv) no hash is reused
    → Unique h̅
    → Disjoint h̅ (codom sechash)
      ------------------------------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ


  -- ** Stipulation: authorizing deposits
  [3] : ∀ {Rˢ ⟨G⟩C} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
          {vad : ValidAdvertisement ⟨G⟩C}

    → lastCfg Rˢ ≡ (` ⟨G⟩C ∣ Γ₀ at t)
    → let
        α  = auth-init[ A , ⟨G⟩C , x ]
        Γ  = ` ⟨G⟩C ∣ Γ₀ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}

        -- invoke compiler
        txout″ : namesʳ ⟨G⟩C ↦ TxInput
        txout″ = weaken-↦ txout′ {!!}

        sechash″ : namesˡ ⟨G⟩C ↦ ℤ
        sechash″ = weaken-↦ sechash′ {!!}

        Tᵢₙᵢₜ : ∃Tx
        Tᵢₙᵢₜ = L.NE.head $ bitml-compiler ⟨G⟩C vad {!!} {-sechash″-} {!!}{-txout″-} K̂ {!!} {-κ′ (here refl)-}

        -- (i) broadcast Tᵢₙᵢₜ , signed with A's private key
        m = [ SIG (K̂ A) Tᵢₙᵢₜ ]
        λᶜ = B →∗∶ m
      in

      -- (ii) Tᵢₙᵢₜ occurs as a message in Rᶜ
      (∃ λ B → (B →∗∶ [ HASH Tᵢₙᵢₜ ]) ∈ Rᶜ)

      -- (iii) broadcast message in Rᶜ
      -- T0D0: make sure that λᶜ is the first occurrence of such a message after Tinit in Rᶜ

      ----------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′


  -- ** Stipulation: activating the contract
  [4] : ∀ {Rˢ ⟨G⟩C} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
          {vad : ValidAdvertisement ⟨G⟩C}
    → let
        G = G ⟨G⟩C
        C = C ⟨G⟩C
        toSpend = persistentDeposits G
        v       = sum $ map (proj₁ ∘ proj₂) toSpend
      in

      -- (i) consume {G}C and its persistent deposits from Rˢ
      lastCfg Rˢ ≡ ( ` (⟨ G ⟩ C) ∣ Γ₀
                   ∣ || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xi ▷ˢ ad ] }) toSpend
                   ∣ || map (_auth[ ♯▷ ad ]) (nub $ participants G)
                   at t)
    → let
        α  = init[ G , C ]
        Γ  = ⟨ C , v ⟩at z ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- invoke compiler
        txout″ : namesʳ ⟨G⟩C ↦ TxInput
        txout″ = weaken-↦ txout′ {!!}

        sechash″ : namesˡ ⟨G⟩C ↦ ℤ
        sechash″ = weaken-↦ sechash′ {!!}

        Tᵢₙᵢₜ : ∃Tx
        Tᵢₙᵢₜ = L.NE.head $ bitml-compiler ⟨G⟩C vad sechash″ txout″ K̂ {!!} {-κ′ (here refl)-}

        -- (ii) append Tᵢₙᵢₜ to the blockchain
        λᶜ = submit Tᵢₙᵢₜ

        -- (iii) sechash = sechash′, κ = κ′, txout extends txout′ with (z ↦ Tᵢₙᵢₜ)
        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}

        txout : Txout Rˢ′
        txout = {!!} -- cons-↦ z (hashTx Tᵢₙᵢₜ at 0) txout′
      in

      ----------------------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′


  -- ** Contract actions: authorize control
  [5] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
          {i : Index c′}
    → let
        d = c′ ‼ i
      in

      -- D ≡ A ∶ D′
      A ∈ authDecorations d

      -- (i) Rˢ contains ⟨C′ , v⟩ₓ with C′ = D + ∑ᵢ Dᵢ
    → lastCfg Rˢ ≡ (⟨ c′ , v ⟩at x ∣ Γ₀ at t)
    → let
        α  = auth-control[ A , x ▷ d ]
        Γ  = ⟨ c′ , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}

        -- (ii) {G}C is the ancestor of ⟨C′ , v⟩ₓ in Rˢ
        ⟨G⟩C , c′∈ = ancestor c′ (v , x) Γ₀

        ad∈ : ⟨G⟩C ∈ proj₁ κ′
        ad∈ = {!!}

        d∈ : d ∈ subtermsᵈ (C ⟨G⟩C)
        d∈ = {!!}

        A∈ : A ∈ participants ⟨G⟩C
        A∈ = {!!}

        -- (iii) broadcast transaction T, as obtained from the compiler, signed by A
        T′ at o = txout′ {!subst _ !} {-(here refl)-} -- txout′(x)

        -- invoke compiler
        txout″ : namesʳ ⟨G⟩C ↦ TxInput
        txout″ = weaken-↦ txout′ {!!}

        sechash″ : namesˡ ⟨G⟩C ↦ ℤ
        sechash″ = weaken-↦ sechash′ {!!}

        T : ∃Tx
        T = {!!}
        -- T = L.NE.head $ Bd d ? d⊆C₀ d (hashTx T′) o v partG 0
        --   where open Bitml-compiler ⟨G⟩C vad {!!} {-sechash″-} {!!}{-txout″-} K̂ {!!} {-κ′ (here refl)-}

        λᶜ = B →∗∶ [ SIGᵖ (proj₂ κ′ ad∈ d∈ A∈) T ]
      in

      -- (v) transaction T has been previously broadcasted in Rᶜ, and λᶜ is the first signature on T after that
      (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ hashTx T ]) Rᶜ)
    → All (λ l → ¬ ∃ λ B → ¬ ∃ λ k → l ≡ B →∗∶ [ SIGᵖ k T ]) (Any-tail ∃λ)

      ----------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

-- put[_,_,_] : Ids → Secrets → Id → Label

  -- ** Contract actions: authorize reveal
  [7] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
          {n : ℕ}
          {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
          {k⃗ : subtermsᵈ (C ⟨G⟩C) ↦ (participants (G ⟨G⟩C) ↦ ℤ)}

    → ∣ m ∣ᵐ ≤ η

      -- (i) in Rˢ, α consumes ⟨C,v⟩y to obtain ⟨A,v⟩ₓ
    → lastCfg Rˢ ≡ (⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀ at t)
    → let
        α  = auth-rev[ A , a ]
        Γ  = A ∶ a ♯ n ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        Δ : List (Secret × Maybe ℕ)
        Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

        h̅ : Message
        h̅ = map (proj₂ ∘ proj₂) Δ×h̅

        k̅ : Message
        k̅ = concatMap codom (codom k⃗)

        a∈ : a ∈ namesˡ Rˢ
        a∈ = {!!}

        -- T0D0: should we search for a signature of this message instead?
        C,h̅,k̅ : Message
        C,h̅,k̅ = C ◇ h̅ ◇ k̅

        -- (i) some participant B broadcasts message m
        λᶜ = B →∗∶ m

        -- (iii) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      -- (ii) in Rᶜ we find ⋯ (B → O ∶ m) (O → B : sechash′(a)) for some B ⋯
      (∃ λ B → (B , m , [ sechash′ a∈ ]) ∈ oracleInteractions Rᶜ)

      -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
    → (∃α : auth-commit[ A , ⟨G⟩C , Δ ] ∈ labels Rˢ)
    → a ∈ namesˡ (G ⟨G⟩C)

      -- ... with a corresponding broadcast of m′=(C,h̅,k̅) in Rᶜ
    → (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) Rᶜ)

      -- (v) λᶜ is the first broadcast of m after the first broadcast of m′
    → All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail ∃λ)

      ----------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Contract actions: split
  [8] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
          {vcis : List (Val × Contracts × Id)}

    → let
        (vs , cs , _) = unzip₃ vcis
        v = sum vs
      in

      c ≡ [ split (zip vs cs) ]
    → lastCfg Rˢ ≡ (⟨ c , v ⟩at y ∣ Γ₀ at t)
    → let
        α  = split[ y ]
        Γ  = || map (λ{ (vi , ci , xi) → ⟨ ci , vi ⟩at xi }) vcis ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (ii) {G}C′ is the ancestor of ⟨[withdraw A], v⟩y in Rˢ
        ⟨G⟩C′ , c∈ = ancestor c (v , x) Γ₀

        -- (iii) submit transaction T, where T is the first transaction of Bd(D,D,T′,o,v,PartG,0)
        T′ at o = txout′ {! !}

        -- invoke compiler
        txout″ : namesʳ ⟨G⟩C ↦ TxInput
        txout″ = {!!}

        sechash″ : namesˡ ⟨G⟩C ↦ ℤ
        sechash″ = {!!}

        T : ∃Tx
        T = {!!}
        -- T = L.NE.head $ Bd d ? d⊆C₀ d (hashTx T′) o v partG 0
        --   where open Bitml-compiler ⟨G⟩C vad {!!} {-sechash″-} {!!}{-txout″-} K̂ {!!} {-κ′ (here refl)-}

        λᶜ = submit T

        -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
        txout : Txout Rˢ′
        txout = {!!} -- cons-↦ x (T , 0) txout′

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      ----------------------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Contract actions: withdraw
  [9] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
      -- (i) in Rˢ, α consumes ⟨C,v⟩y to obtain ⟨A,v⟩ₓ
    → c ≡ [ withdraw A ]
    → lastCfg Rˢ ≡ (⟨ c , v ⟩at y ∣ Γ₀ at t)
    → let
        α  = withdraw[ A , v , y ]
        Γ  = ⟨ A has v ⟩at x ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (ii) {G}C′ is the ancestor of ⟨[withdraw A], v⟩y in Rˢ
        ⟨G⟩C′ , c∈ = ancestor c (v , x) Γ₀

        -- (iii) submit transaction T, where T is the first transaction of Bd(D,D,T′,o,v,PartG,0)
        T′ at o = txout′ {! !}

        -- invoke compiler
        txout″ : namesʳ ⟨G⟩C ↦ TxInput
        txout″ = {!!}

        sechash″ : namesˡ ⟨G⟩C ↦ ℤ
        sechash″ = {!!}

        T : ∃Tx
        T = {!!}
        -- T = L.NE.head $ Bd d ? d⊆C₀ d (hashTx T′) o v partG 0
        --   where open Bitml-compiler ⟨G⟩C vad {!!} {-sechash″-} {!!}{-txout″-} K̂ {!!} {-κ′ (here refl)-}

        λᶜ = submit T

        -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
        txout : Txout Rˢ′
        txout = {!!} -- cons-↦ x (T , 0) txout′

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      ----------------------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: authorize join
  [10] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀ at t)
    → let
        α  = auth-join[ A , x ↔ x′ ]
        Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        x∈ : x ∈ namesʳ Rˢ
        x∈ = {!!}

        x′∈ : x′ ∈ namesʳ Rˢ
        x′∈ = {!!}
      in

      (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                → (l ≡ B →∗∶ [ hashTx (2 , 1 , T) ])
                × (inputs  T ≡ txout′ x∈ ∷ txout′ x′∈ ∷ [])
                × (outputs T ≡ V.[ Ctx 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
                ) Rᶜ)
    → let
        T : ∃Tx
        T = 2 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

        -- (iii) broadcast transaction T, signed by A
        m′ = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)

      ----------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: join
  [11] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀ at t)
    → let
        α  = join[ x ↔ x′ ]
        Γ  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
        Γₜ = Γ at t

        x∈ : x ∈ namesʳ Rˢ
        x∈ = {!!}

        x′∈ : x′ ∈ namesʳ Rˢ
        x′∈ = {!!}

        -- (iii) submit transaction T
        T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
           { inputs  = txout′ x∈ ∷ txout′ x′∈ ∷ []
           ; wit     = wit⊥
           ; relLock = V.replicate 0
           ; outputs = V.[ (v + v′) -redeemableWith- K̂ A ]
           ; absLock = 0 }
        λᶜ = submit T

        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (v) extend txout′ with y↦T₀ (removing {x↦_;x′↦_}), sechash = sechash′, κ = κ′
        txout : Txout Rˢ′
        txout = {!!} -- cons-↦ y (T , 0) $ weaken-↦ ?? txout′

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      ----------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: authorize divide
  [12] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → lastCfg Rˢ ≡ (⟨ A has (v + v′) ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀ at t)
    → let
        α  = auth-divide[ A , x ▷ v , v′ ]
        Γ  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        x∈ : x ∈ namesʳ Rˢ
        x∈ = {!!}
      in

      (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                → (l ≡ B →∗∶ [ hashTx (1 , 2 , T) ])
                × (inputs  T ≡ V.[ txout′ x∈ ])
                × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
                ) Rᶜ)
    → let
        T : ∃Tx
        T = 1 , 2 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

        -- (iii) broadcast transaction T, signed by A
        m′ = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)

      ----------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: divide
  [13] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → lastCfg Rˢ ≡ (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀ at t)
    → let
        α  = divide[ x ▷ v , v′ ]
        Γ  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
        Γₜ = Γ at t

        x∈ : x ∈ namesʳ Rˢ
        x∈ = {!!}

        -- (iii) submit transaction T
        T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
           { inputs  = V.[ txout′ x∈ ]
           ; wit     = wit⊥
           ; relLock = V.replicate 0
           ; outputs = (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ []
           ; absLock = 0 }
        λᶜ = submit T

        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (v) extend txout′ with {y↦T₀, y′↦T₁} (removing x↦T₀), sechash = sechash′, κ = κ′
        txout : Txout Rˢ′
        txout = {!!} -- cons-↦ y (T , 0) $ cons-↦ y′ (T , 1) $ weaken-↦ ?? txout′

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      ----------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: authorize donate
  [14] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ Γ₀ at t)

    → let
        α  = auth-donate[ A , x ▷ᵈ B′ ]
        Γ  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        x∈ : x ∈ namesʳ Rˢ
        x∈ = {!!}
      in

      (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                → (l ≡ B →∗∶ [ hashTx (1 , 1 , T) ])
                × (inputs  T ≡ V.[ txout′ x∈ ])
                × (outputs T ≡ V.[ v -redeemableWith- K̂ B′ ])
                ) Rᶜ)
    → let
        T : ∃Tx
        T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

        -- (iii) broadcast transaction T, signed by A
        m′ = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)

      ----------------------------------------------------------------------------------
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: donate
  [15] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀ at t)

    → let
        α  = donate[ x ▷ᵈ B′ ]
        Γ  = ⟨ B′ has v ⟩at y ∣ Γ
        Γₜ = Γ at t

        x∈ : x ∈ namesʳ Rˢ
        x∈ = {!!}

        -- (iii) submit transaction T
        T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
           { inputs  = V.[ txout′ x∈ ]
           ; wit     = wit⊥
           ; relLock = V.replicate 0
           ; outputs = V.[ v -redeemableWith- K̂ B′ ]
           ; absLock = 0 }
        λᶜ = submit T

        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
        txout : Txout Rˢ′
        txout = {!!} -- cons-↦ y (T , 0) $ cons-↦ y′ (T , 1) $ weaken-↦ ?? txout′

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      ----------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** After
  [18] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → let
        α  = delay[ δ ]
        Γ at t = lastCfg Rˢ
        Γₜ = Γ at (t + δ)
        λᶜ = delay δ
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in
      ----------------------------------------------------------------------------------
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′


data coher₁₂ where

  -- ** Deposits: authorize destroy
  [16] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
           {ds : List (Participant × Value × Id)} {j : Index ds}

    → let
        k  = length ds
        xs = map (proj₂ ∘ proj₂) ds
        A  = proj₁ (ds ‼ j)
        j′ = ‼-map {xs = ds} j
        Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
      in

      -- (ii) in Rˢ we find ⟨Bᵢ,vᵢ⟩yᵢ for i ∈ 1..k
      lastCfg Rˢ ≡ (Δ ∣ Γ₀ at t)

    → let
        α  = auth-destroy[ A , xs , j′ ]
        Γ  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        xs⊆ : xs ⊆ namesʳ Rˢ
        xs⊆ = {!!}
      in

      -- (iii) in Rᶜ we find B → ∗ ∶ T, for some T having txout′(yᵢ) as inputs (+ possibly others)
      (T : Tx i 0)
    → mapWith∈ xs (txout′ ∘ xs⊆) ⊆ V.toList (inputs T)
    → (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ hashTx (_ , _ , T) ]) Rᶜ)

    → let
        -- (iv) broadcast transaction T, signed by A
        m = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m

        -- (vii) txout = txout′, sechash = sechash′, κ = κ′
        namesʳ≡ : namesʳ Rˢ′ ≡ namesʳ Rˢ
        namesʳ≡ = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      -- (v) λᶜ is the first broadcast of m in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m) (Any-tail T∈)

      -- (vi) λᶜ does not correspond to any *other* symbolic move
    → (∀ α′ Γₜ (txout′ : Txout Rˢ) (sechash′ : Sechash Rˢ)
               (txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ)) (sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ))
         → α′ ≢ α
         → ¬ coher₁₁ Rˢ α′ Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ)
      ----------------------------------------------------------------------------------
    → coher₁₂ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ namesʳ≡) sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

  -- ** Deposits: destroy
  [17] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
           {ds : List (Participant × Value × Id)} {j : Index ds}

    → let
        xs  = map (proj₂ ∘ proj₂) ds
        Δ   = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                       (enumerate ds)

        xs⊆ : xs ⊆ namesʳ Rˢ
        xs⊆ = {!!}
      in

      -- (ii) in Rˢ, α assumes ⟨Aᵢ,vᵢ⟩xᵢ to obtain 0
      lastCfg Rˢ ≡ (Δ ∣ Γ₀ at t)

    → (T : Tx i 0)
    → mapWith∈ xs (txout′ ∘ xs⊆) ⊆ V.toList (inputs T)

    → let
        α  = destroy[ xs ]
        Γ  = Γ₀
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- (iii) submit transaction T
        λᶜ = submit (_ , _ , T)

        -- remove {⋯ xᵢ ↦ (Tᵢ,j) ⋯} from txout′
        txout : Txout Rˢ′
        txout = {!!}

        namesˡ≡ : namesˡ Rˢ′ ≡ namesˡ Rˢ
        namesˡ≡ = {!!}
      in

      -- (iv) λᶜ does not correspond to any *other* symbolic move
      (∀ α′ Γₜ (txout′ : Txout Rˢ) (sechash′ : Sechash Rˢ)
               (txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ)) (sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ))
         → α′ ≢ α
         → ¬ coher₁₁ Rˢ α′ Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ)
      ----------------------------------------------------------------------
    → coher₁₂ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ (sechash′ ↑ namesˡ≡) κ′ κ′

data coher₂ Rˢ txout where

  [1] :

      Disjoint (V.toList (inputs (proj₂ (proj₂ T)))) (codom txout)
      -----------------------------------------------------------------
    → coher₂ Rˢ txout (submit T)

  [2] :

      (λᶜ ≡ A →O∶ m)
    ⊎ (λᶜ ≡ O→ A ∶ m)
      ------------------
    → coher₂ Rˢ txout λᶜ

  [3] : let λᶜ = A →∗∶ m in

      -- λᶜ does not correspond to any symbolic move
      (∀ α Γₜ Rᶜ (txout′ : Txout Rˢ) (sechash′ : Sechash Rˢ)
                 (txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ)) (sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ))
                 κ′ κ
         → ¬ coher₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ)
      -----------------------------------------------------------------------------------------------------
    → coher₂ Rˢ txout λᶜ

data coher where
-- namesʳ Rˢ ↦ ∃(T , o). T ∈ trans Rᶜ

  base : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

      -- (i) initial Rˢ
    → Rˢ ≡ (Γ₀ at 0) ∙
    → S.Initial Γ₀
      -- (ii) initial Rᶜ
    → C.Initial Rᶜ
      -- (iii) generation of public keys, we do not consider that here
      -- (iv) txout { ⟨ A , v ⟩ₓ ∈ Γ₀ ↦ T₀{value = $ v, spendable with K̂(A)(rₐ)} ∈ T₀ }
    -- → ?
      -- (v) dom sechash = ∅
    → dom sechash′ ≡ []
      -- (vi) dom κ = ∅
    → proj₁ κ′ ≡ []
      ------------------------------
    → coher Rˢ Rᶜ txout′ sechash′ κ′

  step₁ : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}
                 {txout : Txout (Γₜ ∷⟦ α ⟧ Rˢ)} {sechash : Sechash (Γₜ ∷⟦ α ⟧ Rˢ)}

    → coher Rˢ Rᶜ txout′ sechash′ κ′
    → coher₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
      -------------------------------------------------------
    → coher (Γₜ ∷⟦ α ⟧ Rˢ) (Rᶜ L.∷ʳ λᶜ) txout sechash κ

  step₂ : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ}

    → coher Rˢ Rᶜ txout′ sechash′ κ′
    → coher₂ Rˢ txout′ λᶜ
      ----------------------------------------
    → coher Rˢ (Rᶜ L.∷ʳ λᶜ) txout′ sechash′ κ′

_~_ _≁_ : S.Run → C.Run → Set
Rˢ ~ Rᶜ = Σ[ txout ∈ Txout Rˢ ] Σ[ sechash ∈ Sechash Rˢ ] ∃ (coher Rˢ Rᶜ txout sechash)
  -- = ∃ (∃ (∃ (coher Rˢ Rᶜ)))
Rˢ ≁ Rᶜ = ¬ (Rˢ ~ Rᶜ)
