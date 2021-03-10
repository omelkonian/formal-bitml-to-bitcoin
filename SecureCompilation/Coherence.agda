open import Data.List.Membership.Propositional.Properties

open import Prelude.Init hiding (T)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Collections
open import Prelude.Monoid
open import Prelude.Ord using (maximum)

open import Bitcoin.Crypto using (KeyPair)

module SecureCompilation.Coherence
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel.Strategy Participant Honest as S
  renaming (Value to Val)
open import SymbolicModel.Helpers Participant Honest
open import ComputationalModel.Strategy Participant Honest finPart keypairs as C

open import Bitcoin.Crypto as C
open import Bitcoin.BasicTypes as C hiding (t; t′)
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

_-redeemableWith-_ : Val → KeyPair → ∃TxOutput
v -redeemableWith- k = Ctx 1 , record {value = v;  validator = ƛ (versig [ k ] [ # 0 ])}

-- T0D0: redefine Message ≈ ℤ ??
SIGᵐ : KeyPair → Message → Message
SIGᵐ k = map (SIG k)

private
  variable
    ⟨G⟩C ⟨G⟩C′ ⟨G⟩C″ : Advertisement
    T T′ : ∃Tx

-- ** Types and notation.
data coher : (Rˢ : S.Run) (Rᶜ : C.Run) (txout : Txout Rˢ) (sechash : Sechash Rˢ) (κ : 𝕂 Rˢ) → Set
data coher₂ (Rˢ : S.Run) (txout : Txout Rˢ) : C.Label → Set
data coher₁ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
  (txout′ : Txout Rˢ) (txout : Txout Rˢ′)
  (sechash′ : Sechash Rˢ) (sechash : Sechash Rˢ′)
  (κ′ : 𝕂 Rˢ) (κ : 𝕂 Rˢ′)
  → Set
data coher₁₁ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
  (txout′ : Txout Rˢ) (txout : Txout Rˢ′)
  (sechash′ : Sechash Rˢ) (sechash : Sechash Rˢ′)
  (κ′ : 𝕂 Rˢ) (κ : 𝕂 Rˢ′)
  → Set
data coher₁₂ :
  (Rˢ : S.Run) (α : S.Label) (Γₜ : TimedConfiguration)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
  (txout′ : Txout Rˢ) (txout : Txout Rˢ′)
  (sechash′ : Sechash Rˢ) (sechash : Sechash Rˢ′)
  (κ′ : 𝕂 Rˢ) (κ : 𝕂 Rˢ′)
  → Set

-- ** Definitions.
data coher₁ where
  [L] : ∀ {Rˢ} → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
          {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {txout : Txout Rˢ′} {sechash : Sechash Rˢ′} {κ′ : 𝕂 Rˢ} {κ : 𝕂 Rˢ′}
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
    → coher₁  Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

  [R] : ∀ {Rˢ} → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
          {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {txout : Txout Rˢ′} {sechash : Sechash Rˢ′} {κ′ : 𝕂 Rˢ} {κ : 𝕂 Rˢ′}
    → coher₁₂ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
    → coher₁  Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

data coher₁₁ where

  -- ** Advertising a contract
  [1] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

    → let
        Γ₀ at t = lastCfg Rˢ

        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        α  = advertise[ ⟨G⟩C ]
        Γ  = ` ⟨G⟩C ∣ Γ₀
        Γₜ = Γ at t
        λᶜ = A →∗∶ C
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- txout′ = txout, sechash′ = sechash, κ′ = κ
      in
      --——————————————————————————————————————————————————————————————————————
      coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ refl) sechash′ (sechash′ ↑ refl) κ′ (κ′ ↑ refl)

  -- ** Stipulation: committing secrets
  [2] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
          {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
          {k⃗ : subtermsᶜ′ (C ⟨G⟩C) ↦ (nub-participants (G ⟨G⟩C) ↦ KeyPair)}

      -- T0D0: Γᵣₛ does not necessary keep ⟨G⟩C in its head, replace _≡_ with _≈_?
    → (cfg≡ : lastCfg Rˢ ≡ (` ⟨G⟩C ∣ Γ₀ at t))
    → let
        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        Δ : List (Secret × Maybe ℕ)
        Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

        as : Secrets
        as = map proj₁ Δ

        Δᶜ : Configuration
        Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ

        h̅ : List ℤ -- ≈ Message
        h̅ = map (proj₂ ∘ proj₂) Δ×h̅

        k̅ : List ℤ -- ≈ Message
        k̅ = concatMap (map pub ∘ codom) (codom k⃗)

        C,h̅,k̅ : Message
        C,h̅,k̅ = C ◇ h̅ ◇ k̅

        C,h̅,k̅ₐ : Message
        C,h̅,k̅ₐ = SIGᵐ (K A) C,h̅,k̅

        α  = auth-commit[ A , ⟨G⟩C , Δ ]
        Γ  = ` ⟨G⟩C ∣ Γ₀ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
        Γₜ = Γ at t
        λᶜ = B →∗∶ C,h̅,k̅ₐ
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        open H₂ (` ⟨G⟩C ∣ Γ₀) A A ⟨G⟩C Δ
        open H₂′ Rˢ Rˢ′ (cong cfg cfg≡) refl

        -- (v) txout = txout′
        txout : Txout Rˢ′
        txout = txout↝ txout′

        -- (vi) extend sechash′
        sechash″ : as ↦ ℤ
        sechash″ a∈ =
          let _ , a×m∈ , _    = ∈-map⁻ proj₁ a∈
              (_ , _ , z) , _ = ∈-map⁻ (λ{ (s , mn , _) → s , mn }) a×m∈
          in z

        sechash : Sechash Rˢ′
        sechash = sechash↝ sechash′ sechash″

        -- (vii) extend κ′
        κ : 𝕂 Rˢ′
        κ = κ↝ κ′ k⃗
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
      --——————————————————————————————————————————————————————————————————————
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ


  -- ** Stipulation: authorizing deposits
  [3] : ∀ {Rˢ ⟨G⟩C} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
          {vad : ValidAdvertisement ⟨G⟩C}

    → (cfg≡ : lastCfg Rˢ ≡ (` ⟨G⟩C ∣ Γ₀ at t))
    → let
        ⟨ G ⟩ C = ⟨G⟩C
        partG = nub-participants G

        α  = auth-init[ A , ⟨G⟩C , x ]
        Γ  = ` ⟨G⟩C ∣ Γ₀ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
        Γₜ = Γ at t
        Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

        -- invoke compiler
        Tᵢₙᵢₜ : ∃Tx
        Tᵢₙᵢₜ =
          let -- invoke compiler
            names⊆ : names G ⊆ names Rˢ
            names⊆ = {!!}

            txout″ : namesʳ G ↦ TxInput
            txout″ = weaken-↦ txout′ {!!}

            sechash″ : namesˡ G ↦ ℤ
            sechash″ = weaken-↦ sechash′ {!!}

            K : partG ↦ KeyPair
            K {p} _ = K̂ p

            ad∈ : ⟨G⟩C ∈ advertisements Rˢ
            ad∈ = {!!} -- (∈-++⁺ˡ $ ∈-++⁺ˡ {xs = advertisements (` ⟨G⟩C ∣ Γ₀)} $ here refl)

            K₂ : subtermsᶜ′ C ↦ (partG ↦ KeyPair)
            K₂ = κ′ ad∈
          in
            proj₁ $ bitml-compiler {g = G} {ds = C} vad sechash″ txout″ K K₂

        -- (i) broadcast Tᵢₙᵢₜ , signed with A's private key
        m = [ SIG (K̂ A) Tᵢₙᵢₜ ]
        λᶜ = B →∗∶ m

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        open H₃ (` ⟨G⟩C ∣ Γ₀) A x ⟨G⟩C
        open H₃′ Rˢ Rˢ′ (cong cfg cfg≡) refl

        txout : Txout Rˢ′
        txout = txout↝ txout′

        sechash : Sechash Rˢ′
        sechash = sechash↝ sechash′

        κ : 𝕂 Rˢ′
        κ = κ↝ κ′
      in

      -- (ii) Tᵢₙᵢₜ occurs as a message in Rᶜ
      (∃ λ B → (B →∗∶ [ HASH Tᵢₙᵢₜ ]) ∈ Rᶜ)

      -- (iii) broadcast message in Rᶜ
      -- T0D0: make sure that λᶜ is the first occurrence of such a message after Tinit in Rᶜ

      --——————————————————————————————————————————————————————————————————————
    → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ


--   -- ** Stipulation: activating the contract
--   [4] : ∀ {Γ₀ Rˢ G C} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--     → let
--         ad      = ⟨ G ⟩ C
--         toSpend = persistentDeposits G
--         partG   = nub-participants G
--         v       = sum $ map (proj₁ ∘ proj₂) toSpend
--       in
--       {vad : ValidAdvertisement ad}
--       -- (i) consume {G}C and its persistent deposits from Rˢ
--       (cfg≡ : lastCfg Rˢ ≡
--         ( ` ad ∣ Γ₀
--         ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ] }) toSpend
--         ∣ || map (_auth[ ♯▷ ad ]) partG
--         at t) )
--     → let
--         α  = init[ G , C ]
--         Γ  = ⟨ C , v ⟩at z ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         Tᵢₙᵢₜ : ∃Tx
--         Tᵢₙᵢₜ =
--           let -- invoke compiler
--             txout″ : namesʳ G ↦ TxInput
--             txout″ = weaken-↦ txout′ {!!}

--             sechash″ : namesˡ G ↦ ℤ
--             sechash″ = weaken-↦ sechash′ {!!}

--             K̂ : partG ↦ KeyPair
--             K̂ = {!!}

--             K₂ : subtermsᶜ′ C ↦ (partG ↦ KeyPair)
--             K₂ = {!!} -- κ′ (here refl)
--           in
--             proj₁ $ bitml-compiler {g = G} {ds = C} vad sechash″ txout″ K̂ K₂

--         -- (ii) append Tᵢₙᵢₜ to the blockchain
--         λᶜ = submit Tᵢₙᵢₜ

--         -- (iii) sechash = sechash′, κ = κ′, txout extends txout′ with (z ↦ Tᵢₙᵢₜ)
--         open H₄ G C v z Γ₀ toSpend partG
--         open H₄′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ (hashTx Tᵢₙᵢₜ at 0)

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ


--   -- ** Contract actions: authorize control
--   [5] : ∀ {Rˢ ⟨G⟩C} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--           {c′} {i : Index c′}
--     → let d = c′ ‼ i; d∗ = removeTopDecorations d in

--       -- D ≡ A ∶ D′
--       A ∈ authDecorations d

--       -- (i) Rˢ contains ⟨C′ , v⟩ₓ with C′ = D + ∑ᵢ Dᵢ
--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ c′ , v ⟩at x ∣ Γ₀ at t))

--       -- (ii) {G}C is the ancestor of ⟨C′, v⟩ₓ in Rˢ
--     → (anc : Ancestor Rˢ (c′ , v , x) ⟨G⟩C)

--     → let
--         α  = auth-control[ A , x ▷ d ]
--         Γ  = ⟨ c′ , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         ⟨ G ⟩ C = ⟨G⟩C

--         vad : ValidAdvertisement ⟨G⟩C
--         vad = {!!}

--         ad∈ : ⟨G⟩C ∈ advertisements Rˢ
--         ad∈ = {!!}

--         -- (iii) broadcast transaction T, as obtained from the compiler, signed by A
--         --       where ∙ (T′,o) = txout′(x)
--         --             ∙ T is the first transaction in Bd(d,d,T′,o,v,partG,0)
--         --       i.e. the one corresponding to subterm `d∗ = removeTopDecorations d`
--         T : ∃Tx
--         T =
--           let
--             -- invoke compiler
--             txout″ : namesʳ G ↦ TxInput
--             txout″ = weaken-↦ txout′ {!!}

--             sechash″ : namesˡ G ↦ ℤ
--             sechash″ = weaken-↦ sechash′ {!!}

--             K̂ : nub-participants G ↦ KeyPair
--             K̂ = {!!}

--             K₂ : subtermsᶜ′ C ↦ (nub-participants G ↦ KeyPair)
--             K₂ = κ′ ad∈

--             -- retrieve transaction for specific subterm
--             d∈₀ : d ∈ subtermsᶜ′ C
--             d∈₀ = Ancestor⇒∈ {Rˢ} anc (∈-lookup i)

--             d∗∈ : d∗ ∈ subtermsᵃ⁺ ⟨G⟩C
--             d∗∈ = {!!}
--           in
--             proj₂ (bitml-compiler {g = G} {ds = C} vad sechash″ txout″ K̂ K₂) d∗∈

--         d∈′ : d ∈ subtermsᶜ′ C
--         d∈′ = {!!}

--         A∈ : A ∈ nub-participants G
--         A∈ = {!!}

--         λᶜ = B →∗∶ [ SIGᵖ (pub $ κ′ ad∈ d∈′ {A} A∈) T ]

--         -- (iv) txout = txout′, sechash = sechash′, κ = κ′
--         open H₅ c′ v x Γ₀ A i
--         open H₅′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (v) transaction T has been previously broadcasted in Rᶜ, and λᶜ is the first signature on T after that
--       (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ hashTx T ]) Rᶜ)
--     → All (λ l → ¬ ∃ λ B → ¬ ∃ λ k → l ≡ B →∗∶ [ SIGᵖ k T ]) (Any-tail ∃λ)

--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Contract actions: put
--   [6] : ∀ {Rˢ ⟨G⟩C″} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--           {i : Index c}
--           {ds : List (Participant × Value × Id)}
--           -- {ss : List (Participant × Secret × ℕ)}
--     → let
--         -- (i) xs = x₁⋯xₖ
--         (_ , vs , xs) = unzip₃ ds
--         Γ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
--         d = c ‼ i; d∗ = removeTopDecorations d
--       in

--       -- ii) in Rˢ, α consumes ⟨D+C,v⟩y and the deposits ⟨Aᵢ,vᵢ⟩ₓᵢ to produce ⟨C′,v′⟩y′
--       --     where D = ⋯ : put⋯reveal⋯.C′
--       --     let t be the maximum deadline in an after in front of D
--       --     T0D0: what should t′ be in case there are not after decorations?
--       d ≡⋯∶ put xs &reveal as if p ⇒ c′
--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ c , v ⟩at y ∣ Γ ∣ Γ′ at t))

--       -- (iii) {G}C″ is the ancestor of ⟨D+C,v⟩y in Rˢ
--     → (anc : Ancestor Rˢ (c , v , y) ⟨G⟩C″)

--     → let
--         α  = put[ xs , as , y ]
--         Γ  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ′
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         ⟨ G ⟩ C″ = ⟨G⟩C″
--         partG = nub-participants G

--         vad : ValidAdvertisement ⟨G⟩C″
--         vad = {!!}

--         -- (iv) submit transaction T
--         --      where ∙ (T′,o) = txout′(y)
--         --            ∙ T is the first transaction in Bc(c′,d,T′,o,v′,x⃗,partG,t)
--         --      i.e. the one corresponding to subterm `d∗ = put xs &reveal as if p → c′`
--         T : ∃Tx
--         T =
--           let
--             -- invoke compiler
--             txout″ : namesʳ G ↦ TxInput
--             txout″ = weaken-↦ txout′ {!!}

--             sechash″ : namesˡ G ↦ ℤ
--             sechash″ = weaken-↦ sechash′ {!!}

--             K : partG ↦ KeyPair
--             K {p} _ = K̂ p

--             ad∈ : ⟨G⟩C″ ∈ advertisements Rˢ
--             ad∈ = {!!} -- (∈-++⁺ˡ $ ∈-++⁺ˡ {xs = advertisements (` ⟨G⟩C ∣ Γ₀)} $ here refl)

--             K₂ : subtermsᶜ′ C″ ↦ (partG ↦ KeyPair)
--             K₂ = κ′ ad∈

--             -- retrieve transaction for specific subterm
--             d∗∈ : d∗ ∈ subtermsᶜ⁺ C″
--             d∗∈ = {!!}
--           in
--             proj₂ (bitml-compiler {g = G} {ds = C″} vad sechash″ txout″ K K₂) d∗∈

--         λᶜ = submit T

--         -- (v) extend txout′ with {y′↦(T,0)}, sechash = sechash′, κ = κ′
--         open H₆ c v y c′ y′ ds Γ′
--         open H₆′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ (hashTx T at 0)

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Contract actions: authorize reveal
--   [7] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--           {n : ℕ}
--           {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
--           {k⃗ : subtermsᶜ′ (C ⟨G⟩C) ↦ (participants (G ⟨G⟩C) ↦ ℤ)}

--     → ∣ m ∣ᵐ ≤ η
--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀ at t))

--     → let
--         α  = auth-rev[ A , a ]
--         Γ  = A ∶ a ♯ n ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         C : Message
--         C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

--         Δ : List (Secret × Maybe ℕ)
--         Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

--         h̅ : Message
--         h̅ = map (proj₂ ∘ proj₂) Δ×h̅

--         k̅ : Message
--         k̅ = concatMap codom (codom k⃗)

--         a∈ : a ∈ namesˡ Rˢ
--         a∈ = {!!}

--         -- T0D0: should we search for a signature of this message instead?
--         C,h̅,k̅ : Message
--         C,h̅,k̅ = C ◇ h̅ ◇ k̅

--         -- (i) some participant B broadcasts message m
--         λᶜ = B →∗∶ m

--         -- (iii) txout = txout′, sechash = sechash′, κ = κ′
--         open H₇ A a n Γ₀
--         open H₇′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (ii) in Rᶜ we find ⋯ (B → O ∶ m) (O → B : sechash′(a)) for some B ⋯
--       (∃ λ B → (B , m , [ sechash′ {a} a∈ ]) ∈ oracleInteractions Rᶜ)

--       -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
--     → (∃α : auth-commit[ A , ⟨G⟩C , Δ ] ∈ labels Rˢ)
--     → a ∈ namesˡ (G ⟨G⟩C)

--       -- ... with a corresponding broadcast of m′=(C,h̅,k̅) in Rᶜ
--     → (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) Rᶜ)

--       -- (v) λᶜ is the first broadcast of m after the first broadcast of m′
--     → All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail ∃λ)

--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Contract actions: split
--   [8] : ∀ {Rˢ ⟨G⟩C′} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--           {i : Index c}
--           {vcis : List (Val × Contracts × Id)}

--     → let
--         (vs , cs , _) = unzip₃ vcis
--         v = sum vs
--         d = c ‼ i; d∗ = removeTopDecorations d
--       in
--       -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨C₀,v₀⟩ₓ₀ | ⋯ | ⟨Cₖ,vₖ⟩ₓₖ
--       --     where D = ⋯ : split vs → cs
--       --     let t be the maximum deadline in an after in front of D
--       --     T0D0: what should t′ be in case there are not after decorations?
--       d ≡⋯∶ split (zip vs cs)
--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ c , v ⟩at y ∣ Γ₀ at t))

--       -- (iii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
--     → (anc : Ancestor Rˢ (c , v , y) ⟨G⟩C′)

--     → let
--         t = maximum t′ $ timeDecorations d
--         α  = split[ y ]
--         Γ  = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         ⟨ G ⟩ C = ⟨G⟩C′
--         partG = nub-participants G

--         vad : ValidAdvertisement ⟨G⟩C′
--         vad = {!!}

--         -- (iii) submit transaction T
--         --       where ∙ (T′,o) = txout′(y)
--         --             ∙ T is the first transaction in Bpar(cs,d,T′,o,partG,t)
--         --       i.e. the one corresponding to subterm `d∗ = split (zip vs cs)`
--         T : ∃Tx
--         T =
--           let -- invoke compiler
--             txout″ : namesʳ G ↦ TxInput
--             txout″ = weaken-↦ txout′ {!!}

--             sechash″ : namesˡ G ↦ ℤ
--             sechash″ = weaken-↦ sechash′ {!!}

--             K : partG ↦ KeyPair
--             K {p} _ = K̂ p

--             ad∈ : ⟨G⟩C′ ∈ advertisements Rˢ
--             ad∈ = {!!} -- (∈-++⁺ˡ $ ∈-++⁺ˡ {xs = advertisements (` ⟨G⟩C ∣ Γ₀)} $ here refl)

--             K₂ : subtermsᶜ′ C ↦ (partG ↦ KeyPair)
--             K₂ = κ′ ad∈

--             -- retrieve transaction for specific subterm
--             d∈₀ : d ∈ subtermsᶜ′ C
--             d∈₀ = Ancestor⇒∈ {Rˢ} anc (∈-lookup i)

--             d∗∈ : d∗ ∈ subtermsᵃ⁺ ⟨G⟩C′
--             d∗∈ = {!!}
--           in
--             proj₂ (bitml-compiler {g = G} {ds = C} vad sechash″ txout″ K K₂) d∗∈

--         λᶜ = submit T

--         -- (iv) extend txout′ with {xᵢ ↦ (T,i)}, sechash = sechash′, κ = κ′
--         open H₈ c v y Γ₀ vcis
--         open H₈′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ ((hashTx T at_) ∘ F.toℕ ∘ L.Any.index)

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Contract actions: withdraw
--   [9] : ∀ {Rˢ ⟨G⟩C′} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--           {i : Index c}
--     → let d = c ‼ i; d∗ = removeTopDecorations d in
--       -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨A,v⟩ₓ (where D = ⋯ : withdraw A)
--       d ≡⋯∶ withdraw A
--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ c , v ⟩at y ∣ Γ₀ at t))

--       -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
--     → (anc : Ancestor Rˢ (c , v , y) ⟨G⟩C′)
--     → let
--         α  = withdraw[ A , v , y ]
--         Γ  = ⟨ A has v ⟩at x ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         ⟨ G ⟩ C = ⟨G⟩C′
--         partG = nub-participants G

--         vad : ValidAdvertisement ⟨G⟩C′
--         vad = {!!}
--         -- T0D0 how to ensure the ad is valid??

--         --   ∙ T′ at o = txout′(x)
--         --   ∙ T is the first transaction of Bd(d,d,T′,o,v,partG,0)
--         -- i.e.
--         -- (iii) submit transaction T
--         --       where ∙ (T′,o) = txout′(y)
--         --             ∙ T is the first transaction in Bd(d,d,T′,o,v,partG,0)
--         --       i.e. the one corresponding to subterm `d∗ = withdraw A`
--         T : ∃Tx
--         T =
--           let -- invoke compiler
--             txout″ : namesʳ G ↦ TxInput
--             txout″ = weaken-↦ txout′ {!!}

--             sechash″ : namesˡ G ↦ ℤ
--             sechash″ = weaken-↦ sechash′ {!!}

--             K : partG ↦ KeyPair
--             K {p} _ = K̂ p

--             ad∈ : ⟨G⟩C′ ∈ advertisements Rˢ
--             ad∈ = {!!} -- (∈-++⁺ˡ $ ∈-++⁺ˡ {xs = advertisements (` ⟨G⟩C ∣ Γ₀)} $ here refl)

--             K₂ : subtermsᶜ′ C ↦ (partG ↦ KeyPair)
--             K₂ = κ′ ad∈

--             -- retrieve transaction for specific subterm
--             d∈₀ : d ∈ subtermsᶜ′ C
--             d∈₀ = Ancestor⇒∈ {Rˢ} anc (∈-lookup i)

--             d∗∈ : d∗ ∈ subtermsᵃ⁺ ⟨G⟩C′
--             d∗∈ = {!!}
--           in
--             proj₂ (bitml-compiler {g = G} {ds = C} vad sechash″ txout″ K K₂) d∗∈

--         λᶜ = submit T

--         -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
--         open H₉ c v y Γ₀ A x
--         open H₉′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ (hashTx T at 0)

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: authorize join
--   [10] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀ at t))

--     → let
--         α  = auth-join[ A , x ↔ x′ ]
--         Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = {!!}

--         x′∈ : x′ ∈ namesʳ Rˢ
--         x′∈ = {!!}
--       in

--       (∃λ : Any (λ l → ∃ λ B → ∃ λ T
--                 → (l ≡ B →∗∶ [ hashTx (2 , 1 , T) ])
--                 × (inputs  T ≡ txout′ {x} x∈ ∷ txout′ {x′} x′∈ ∷ [])
--                 × (outputs T ≡ V.[ Ctx 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
--                 ) Rᶜ)
--     → let
--         T : ∃Tx
--         T = 2 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

--         -- (iii) broadcast transaction T, signed by A
--         m′ = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m′

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₀ A v x v′ x′ Γ₀
--         open H₁₀′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)

--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: join
--   [11] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀ at t))

--     → let
--         α  = join[ x ↔ x′ ]
--         Γ  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
--         Γₜ = Γ at t

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = {!!}

--         x′∈ : x′ ∈ namesʳ Rˢ
--         x′∈ = {!!}

--         -- (ii) submit transaction T
--         T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
--            { inputs  = txout′ {x} x∈ ∷ txout′ {x′} x′∈ ∷ []
--            ; wit     = wit⊥
--            ; relLock = V.replicate 0
--            ; outputs = V.[ (v + v′) -redeemableWith- K̂ A ]
--            ; absLock = 0 }
--         λᶜ = submit T

--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         -- (iii) extend txout′ with y↦T₀ (removing {x↦_;x′↦_}), sechash = sechash′, κ = κ′
--         open H₁₁ A v x v′ x′ y Γ₀
--         open H₁₁′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ (hashTx T at 0)

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: authorize divide (similar to [10])
--   [12] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A has (v + v′) ⟩at x ∣ Γ₀ at t))

--     → let
--         α  = auth-divide[ A , x ▷ v , v′ ]
--         Γ  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = {!!}
--       in

--       (∃λ : Any (λ l → ∃ λ B → ∃ λ T
--                 → (l ≡ B →∗∶ [ hashTx (1 , 2 , T) ])
--                 × (inputs  T ≡ V.[ txout′ {x} x∈ ])
--                 × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
--                 ) Rᶜ)
--     → let
--         T : ∃Tx
--         T = 1 , 2 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

--         -- (iii) broadcast transaction T, signed by A
--         m′ = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m′

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₂ A v v′ x Γ₀
--         open H₁₂′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)

--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: divide (dimilar to [11])
--   [13] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀ at t))

--     → let
--         α  = divide[ x ▷ v , v′ ]
--         Γ  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
--         Γₜ = Γ at t

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = {!!}

--         -- (iii) submit transaction T
--         T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
--            { inputs  = V.[ txout′ {x} x∈ ]
--            ; wit     = wit⊥
--            ; relLock = V.replicate 0
--            ; outputs = (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ []
--            ; absLock = 0 }
--         λᶜ = submit T

--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         -- (v) extend txout′ with {y↦T₀, y′↦T₁} (removing x↦T₀), sechash = sechash′, κ = κ′
--         open H₁₃ A v v′ x Γ₀ y y′
--         open H₁₃′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ ((hashTx T at 0) , (hashTx T at 1))

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: authorize donate (similar to [10])
--   [14] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ Γ₀ at t))

--     → let
--         α  = auth-donate[ A , x ▷ᵈ B′ ]
--         Γ  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = {!!}
--       in

--       (∃λ : Any (λ l → ∃ λ B → ∃ λ T
--                 → (l ≡ B →∗∶ [ hashTx (1 , 1 , T) ])
--                 × (inputs  T ≡ V.[ txout′ {x} x∈ ])
--                 × (outputs T ≡ V.[ v -redeemableWith- K̂ B′ ])
--                 ) Rᶜ)
--     → let
--         T : ∃Tx
--         T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

--         -- (iii) broadcast transaction T, signed by A
--         m′ = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m′

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₄ A v x Γ₀ B′
--         open H₁₄′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)

--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: donate (similar to [11])
--   [15] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → (cfg≡ : lastCfg Rˢ ≡ (⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀ at t))

--     → let
--         α  = donate[ x ▷ᵈ B′ ]
--         Γ  = ⟨ B′ has v ⟩at y ∣ Γ₀
--         Γₜ = Γ at t

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = {!!}

--         -- (iii) submit transaction T
--         T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
--            { inputs  = V.[ txout′ {x} x∈ ]
--            ; wit     = wit⊥
--            ; relLock = V.replicate 0
--            ; outputs = V.[ v -redeemableWith- K̂ B′ ]
--            ; absLock = 0 }
--         λᶜ = submit T

--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
--         open H₁₅ A v x B′ Γ₀ y
--         open H₁₅′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′ (hashTx T at 0)

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** After
--   [18] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → let
--         α  = delay[ δ ]
--         Γ at t = lastCfg Rˢ
--         Γₜ = Γ at (t + δ)
--         λᶜ = delay δ
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ Rᶜ λᶜ txout′ (txout′ ↑ refl) sechash′ (sechash′ ↑ refl) κ′ (κ′ ↑ refl)


-- data coher₁₂ where

--   -- ** Deposits: authorize destroy
--   [16] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--            {ds : List (Participant × Value × Id)} {j : Index ds}

--     → let
--         k  = length ds
--         xs = map (proj₂ ∘ proj₂) ds
--         A  = proj₁ (ds ‼ j)
--         j′ = ‼-map {xs = ds} j
--         Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
--       in

--       -- (ii) in Rˢ we find ⟨Bᵢ,vᵢ⟩yᵢ for i ∈ 1..k
--       (cfg≡ : lastCfg Rˢ ≡ (Δ ∣ Γ₀ at t))

--     → let
--         α  = auth-destroy[ A , xs , j′ ]
--         Γ  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         xs⊆ : xs ⊆ namesʳ Rˢ
--         xs⊆ = {!!}
--       in

--       -- (iii) in Rᶜ we find B → ∗ ∶ T, for some T having txout′(yᵢ) as inputs (+ possibly others)
--       (T : Tx i 0)
--     → mapWith∈ xs (txout′ ∘ xs⊆) ⊆ V.toList (inputs T)
--     → (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ hashTx (_ , _ , T) ]) Rᶜ)

--     → let
--         -- (iv) broadcast transaction T, signed by A
--         m = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m

--         -- (vii) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₆ ds j Γ₀ A y
--         open H₁₆′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (v) λᶜ is the first broadcast of m in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m) (Any-tail T∈)

--       -- (vi) λᶜ does not correspond to any *other* symbolic move
--     → (∀ α′ Γₜ (txout′ : Txout Rˢ) (sechash′ : Sechash Rˢ) (κ′ : 𝕂 Rˢ)
--          → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
--                (txout : Txout Rˢ′) (sechash : Sechash Rˢ′) (κ : 𝕂 Rˢ′)
--          → α′ ≢ α
--          → ¬ coher₁₁ Rˢ α′ Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ)

--       --——————————————————————————————————————————————————————————————————————

--     → coher₁₂ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

--   -- ** Deposits: destroy
--   [17] : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--            {ds : List (Participant × Value × Id)} {j : Index ds}

--     → let
--         xs  = map (proj₂ ∘ proj₂) ds
--         Δ   = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds)

--         xs⊆ : xs ⊆ namesʳ Rˢ
--         xs⊆ = {!!}
--       in

--       -- (ii) in Rˢ, α assumes ⟨Aᵢ,vᵢ⟩xᵢ to obtain 0
--       (cfg≡ : lastCfg Rˢ ≡ (Δ ∣ Γ₀ at t))

--     → (T : Tx i 0)
--     → mapWith∈ xs (txout′ ∘ xs⊆) ⊆ V.toList (inputs T)

--     → let
--         α  = destroy[ xs ]
--         Γ  = Γ₀
--         Γₜ = Γ at t
--         Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ

--         -- (iii) submit transaction T
--         λᶜ = submit (_ , _ , T)

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         -- remove {⋯ xᵢ ↦ (Tᵢ,j) ⋯} from txout′
--         open H₁₇ ds Γ₀ y
--         open H₁₇′ Rˢ Rˢ′ (cong cfg cfg≡) refl

--         txout : Txout Rˢ′
--         txout = txout↝ txout′

--         sechash : Sechash Rˢ′
--         sechash = sechash↝ sechash′

--         κ : 𝕂 Rˢ′
--         κ = κ↝ κ′
--       in

--       -- (iv) λᶜ does not correspond to any *other* symbolic move
--       (∀ α′ Γₜ (txout′ : Txout Rˢ) (sechash′ : Sechash Rˢ) (κ′ : 𝕂 Rˢ)
--          → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
--                (txout : Txout Rˢ′) (sechash : Sechash Rˢ′) (κ : 𝕂 Rˢ′)
--          → α′ ≢ α
--          → ¬ coher₁₁ Rˢ α′ Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₂ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ

-- data coher₂ Rˢ txout where

--   [1] :

--       Disjoint (V.toList $ inputs $ proj₂ $ proj₂ T) (codom txout)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₂ Rˢ txout (submit T)

--   [2] :

--       (λᶜ ≡ A →O∶ m)
--     ⊎ (λᶜ ≡ O→ A ∶ m)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₂ Rˢ txout λᶜ

--   [3] : let λᶜ = A →∗∶ m in

--       -- λᶜ does not correspond to any symbolic move
--       (∀ α Γₜ Rᶜ (txout′ : Txout Rˢ) (sechash′ : Sechash Rˢ) (κ′ : 𝕂 Rˢ)
--          → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
--                  (txout : Txout Rˢ′) (sechash : Sechash Rˢ′) (κ : 𝕂 Rˢ′)
--          → ¬ coher₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₂ Rˢ txout λᶜ

-- data coher where
-- -- namesʳ Rˢ ↦ ∃(T , o). T ∈ trans Rᶜ

--   base : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--       -- (i) initial Rˢ
--     → Rˢ ≡ (Γ₀ at 0) ∙
--     → S.Initial Γ₀
--       -- (ii) initial Rᶜ
--     → C.Initial Rᶜ
--       -- (iii) generation of public keys, we do not consider that here
--       -- (iv) txout { ⟨ A , v ⟩ₓ ∈ Γ₀ ↦ T₀{value = $ v, spendable with K̂(A)(rₐ)} ∈ T₀ }
--     -- → ?
--       -- (v) dom sechash = ∅
--     → dom sechash′ ≡ []
--       -- (vi) dom κ = ∅
--     → dom κ′ ≡ []
--       --——————————————————————————————————————————————————————————————————————
--     → coher Rˢ Rᶜ txout′ sechash′ κ′

--   step₁ : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}
--           → let Rˢ′ = Γₜ ∷⟦ α ⟧ Rˢ in
--                  {txout : Txout Rˢ′} {sechash : Sechash Rˢ′} {κ : 𝕂 Rˢ′}

--     → coher Rˢ Rᶜ txout′ sechash′ κ′
--     → coher₁ Rˢ α Γₜ Rᶜ λᶜ txout′ txout sechash′ sechash κ′ κ
--       --——————————————————————————————————————————————————————————————————————
--     → coher (Γₜ ∷⟦ α ⟧ Rˢ) (Rᶜ L.∷ʳ λᶜ) txout sechash κ

--   step₂ : ∀ {Rˢ} {txout′ : Txout Rˢ} {sechash′ : Sechash Rˢ} {κ′ : 𝕂 Rˢ}

--     → coher Rˢ Rᶜ txout′ sechash′ κ′
--     → coher₂ Rˢ txout′ λᶜ
--       ----------------------------------------
--     → coher Rˢ (Rᶜ L.∷ʳ λᶜ) txout′ sechash′ κ′

-- _~_ _≁_ : S.Run → C.Run → Set
-- Rˢ ~ Rᶜ = Σ[ txout ∈ Txout Rˢ ] Σ[ sechash ∈ Sechash Rˢ ] ∃ (coher Rˢ Rᶜ txout sechash)
--   -- = ∃ (∃ (∃ (coher Rˢ Rᶜ)))
-- Rˢ ≁ Rᶜ = ¬ (Rˢ ~ Rᶜ)
