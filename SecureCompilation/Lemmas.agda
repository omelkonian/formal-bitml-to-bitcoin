open import Prelude.Init hiding (T)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets

open import Bitcoin.Crypto using (KeyPair)
open import Bitcoin.Tx.Base
open import Bitcoin.Consistency
  hiding (∙)

module SecureCompilation.Lemmas
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel.Strategy Participant Honest as S
  renaming (Value to Val)
  hiding (_∎; begin_)
open import SymbolicModel.Helpers Participant Honest

open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
  hiding (Hon)
open import SecureCompilation.Coherence Participant Honest finPart keypairs η


destruct-Rᶜ : ∀ {Rᶜ₀ Rᶜ : CRun} {λᶜ}
  → Rᶜ₀ ≡ (Rᶜ L.∷ʳ λᶜ)
  → ∃ λ Rᶜ′ → ∃ λ λᶜ′ →
      (Rᶜ′ ≡ Rᶜ) × (λᶜ′ ≡ λᶜ) × (Rᶜ₀ ≡ Rᶜ′ L.∷ʳ λᶜ′)
destruct-Rᶜ {Rᶜ₀} {Rᶜ} {λᶜ} eq = Rᶜ , λᶜ , refl , refl , eq

Consistent-∷ : ConsistentBlockchain (𝔹 $ λᶜ ∷ Rᶜ) → ConsistentBlockchain (𝔹 Rᶜ)
Consistent-∷ {λᶜ} {[]}     vb = ConsistentBlockchain.∙
Consistent-∷ {x₁ →∗∶ x₂} {x ∷ Rᶜ} vb = vb
Consistent-∷ {submit .(_ , _ , tx)} {x ∷ Rᶜ} (vb ⊕ tx ∶- x₁) = vb
Consistent-∷ {delay x₁} {x ∷ Rᶜ} vb = vb
Consistent-∷ {x₁ →O∶ x₂} {x ∷ Rᶜ} vb = vb
Consistent-∷ {O→ x₁ ∶ x₂} {x ∷ Rᶜ} vb = vb

𝔹-initialBroadcasts : ∀ ps → 𝔹 (map ∣initialBroadcasts∣.go ps) ≡ []
𝔹-initialBroadcasts [] = refl
𝔹-initialBroadcasts (_ ∷ ps) = 𝔹-initialBroadcasts ps

δ-initialBroadcasts : ∀ ps → δʳ (map ∣initialBroadcasts∣.go ps) ≡ 0
δ-initialBroadcasts [] = refl
δ-initialBroadcasts (_ ∷ ps) = δ-initialBroadcasts ps

𝔹-initial :
  (cinit : C.Initial Rᶜ)
  → let T₀ , _ = cinit in
    𝔹 Rᶜ ≡ [ T₀ at 0 ]
𝔹-initial (_ , _ , refl) rewrite 𝔹-initialBroadcasts allParticipants | δ-initialBroadcasts allParticipants = refl

utxo-initial :
  (cinit : C.Initial Rᶜ)
  → let
      Bᶜ = 𝔹 Rᶜ
      (_ , _ , T₀) , _ = cinit
    in
      (vb : ConsistentBlockchain Bᶜ)
      → V.All.All (∃Unspent Bᶜ) (outputs T₀)
utxo-initial cinit vb rewrite 𝔹-initial cinit = V.All.tabulate (λ i → 0F , i , (λ{ 0F leq j′ (v , T₀↝T₀) → ↝-irreflexive vb T₀↝T₀ }) , refl)

lemma1-txout :
  (coh : Rˢ ~ Rᶜ) → let txout , _ = coh in
    All (λ{ (∃tx at n) → {!!}}) (codom txout)
lemma1-txout coh = {!!}

-- lemma1-helper :
--   let
--     Γˢ = lastCfg Rˢ
--     Bᶜ = 𝔹 Rᶜ
--   in
--     (coh : Rˢ ~ Rᶜ)
--   → (vb : ConsistentBlockchain Bᶜ) -- [T0D0] we have to make sure that we have a consistent blockchain in our hands at all times
--   → (x∈ : (⟨ A has v ⟩at x) ∈ᶜ Γˢ)
--   → let
--       txout , _ = coh
--       txi = txout (deposit∈Γ⇒namesʳ x∈)
--     in
--   -- → ∃Unspent Bᶜ (v -redeemableWith- K̂ A)
-- lemma1-helper = ?


-- Lemma 1. Let Rˢ ~ Rᶜ. For each deposit ⟨A,v⟩ occurring in Γ_Rˢ, there exists a corresponding
-- unspent transaction output in B_Rᶜ with value v, redeemable with a signature with key K̂_A.
lemma1 :
  let
    Γˢ = lastCfg Rˢ
    Bᶜ = 𝔹 Rᶜ
  in
    Rˢ ~ Rᶜ
  → (vb : ConsistentBlockchain Bᶜ) -- [T0D0] we have to make sure that we have a consistent blockchain in our hands at all times
  → (⟨ A has v ⟩at x) ∈ᶜ Γˢ
  -- → (v -redeemableWith- K̂ A) ∈ utxo Bᶜ vb
  → ∃Unspent Bᶜ (v -redeemableWith- K̂ A)


-- ** base
lemma1 {Rˢ = .((Γ₀ at 0) ∙)} {Rᶜ = Rᶜ} {A} {v} {x} (txout , sechash , κ , base {Γ₀} refl sinit cinit txout≡ sec∅ κ∅) vb d∈ =
  let
    (_ , o , T₀) , _ , Rᶜ≡ = cinit
    oᵢ , txout≡′ , o≡ = txout≡ {A}{v}{x} d∈

    txo : ∃TxOutput
    txo = T₀ ‼ᵒ oᵢ

    Bᶜ = 𝔹 Rᶜ

    qed : ∃Unspent Bᶜ (v -redeemableWith- K̂ A)
    qed = subst (∃Unspent Bᶜ) o≡ (V.All.lookup oᵢ (utxo-initial cinit vb))
  in
    qed

-- ** coher₁
lemma1 {Rˢ = .(_ ∷⟦ _ ⟧ _)} {Rᶜ = λᶜ ∷ Rᶜ} {A} {v} {x}
  (txout , sechash , κ , step₁ coh x₁)
  vb d∈
  = {!!}

-- ** coher₂
lemma1 {Rˢ = Rˢ} {Rᶜ = λᶜ ∷ Rᶜ} {A} {v} {x}
  (txout , sechash , κ , step₂ coh coh₂)
  vb d∈
  -- with oₐᵛ ← v -redeemableWith- K̂ A
  with λᶜ | coh₂
... | .(submit T) | [1] {T = T} inT∉txout
  = qed
  where
    Rˢ~Rᶜ : Rˢ ~ Rᶜ
    Rˢ~Rᶜ = txout , sechash , κ , coh

    Γˢ = lastCfg Rˢ
    Bᶜ = 𝔹 Rᶜ
    λᶜ′ = submit T
    Bᶜ₀ = 𝔹 (λᶜ′ ∷ Rᶜ)

    B≡ : Bᶜ₀ ≡ (T at δʳ Rᶜ) ∷ Bᶜ
    B≡ = refl

    vb′ : ConsistentBlockchain Bᶜ
    vb′ = Consistent-∷ {λᶜ′}{Rᶜ} vb

    oₐᵛ = v -redeemableWith- K̂ A

    IH : ∃Unspent Bᶜ oₐᵛ
    IH = lemma1 {Rˢ}{Rᶜ} Rˢ~Rᶜ vb′ d∈

    qed : ∃Unspent Bᶜ₀ oₐᵛ
    qed = ∃Unspent-∷ vb IH {!!}
... | .(A′ →O∶ m) | [2] {A = A′} {m = m} (inj₁ refl)
  = qed
  where
    Rˢ~Rᶜ : Rˢ ~ Rᶜ
    Rˢ~Rᶜ = txout , sechash , κ , coh

    Γˢ = lastCfg Rˢ
    Bᶜ = 𝔹 Rᶜ
    λᶜ′ = A′ →O∶ m
    Bᶜ₀ = 𝔹 (λᶜ′ ∷ Rᶜ)

    vb′ : ConsistentBlockchain Bᶜ
    vb′ = Consistent-∷ {λᶜ′}{Rᶜ} vb

    oₐᵛ = v -redeemableWith- K̂ A

    IH : ∃Unspent Bᶜ oₐᵛ
    IH = lemma1 {Rˢ}{Rᶜ} Rˢ~Rᶜ vb′ d∈

    -- coh₂ : coher₂ Rˢ txout λᶜ

    qed : ∃Unspent Bᶜ₀ oₐᵛ
    qed = IH
... | .(O→ A′ ∶ m) | [2] {A = A′} {m = m} (inj₂ refl)
  = qed
  where
    Rˢ~Rᶜ : Rˢ ~ Rᶜ
    Rˢ~Rᶜ = txout , sechash , κ , coh

    Γˢ = lastCfg Rˢ
    Bᶜ = 𝔹 Rᶜ
    λᶜ′ = O→ A′ ∶ m
    Bᶜ₀ = 𝔹 (λᶜ′ ∷ Rᶜ)

    vb′ : ConsistentBlockchain Bᶜ
    vb′ = Consistent-∷ {λᶜ′}{Rᶜ} vb

    oₐᵛ = v -redeemableWith- K̂ A

    IH : ∃Unspent Bᶜ oₐᵛ
    IH = lemma1 {Rˢ}{Rᶜ} Rˢ~Rᶜ vb′ d∈

    -- coh₂ : coher₂ Rˢ txout λᶜ

    qed : ∃Unspent Bᶜ₀ oₐᵛ
    qed = IH
... | .(A′ →∗∶ m) | [3] {A = A′} {m = m}  ¬coh₁
  = qed
  where
    Rˢ~Rᶜ : Rˢ ~ Rᶜ
    Rˢ~Rᶜ = txout , sechash , κ , coh

    Γˢ = lastCfg Rˢ
    Bᶜ = 𝔹 Rᶜ
    λᶜ′ = A′ →∗∶ m
    Bᶜ₀ = 𝔹 (λᶜ′ ∷ Rᶜ)

    vb′ : ConsistentBlockchain Bᶜ
    vb′ = Consistent-∷ {λᶜ′}{Rᶜ} vb

    oₐᵛ = v -redeemableWith- K̂ A

    IH : ∃Unspent Bᶜ oₐᵛ
    IH = lemma1 {Rˢ}{Rᶜ} Rˢ~Rᶜ vb′ d∈

    -- coh₂ : coher₂ Rˢ txout λᶜ

    qed : ∃Unspent Bᶜ₀ oₐᵛ
    qed = IH
