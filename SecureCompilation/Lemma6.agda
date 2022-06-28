{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}
-- {-# OPTIONS --auto-inline #-}
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership
open import Prelude.ToN
open import Prelude.General
open import Prelude.ToList
open import Prelude.Sets hiding (toList)
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Sets
open import Prelude.Accessors
open import Prelude.Nary

import Bitcoin.Crypto as BTC

module SecureCompilation.Lemma6
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → BTC.KeyPair × BTC.KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (d; α; Γ; Γ′; Γ″; Γₜ; Γₜ′; t; t′)
open import ComputationalModel Participant Honest finPart keypairs as C
  hiding (∣_∣; `; t; t′)
open import SecureCompilation.Compiler Participant Honest η
open import SecureCompilation.Coherence Participant Honest finPart keypairs η

txout-preserves-value : ∀ {𝕣∗ : ℝ∗ Rˢ} →
  ∙ 𝕣∗ ~′ Rᶜ
    ─────────────────────────────────
    ValuePreservingʳ (ℝ∗⇒ℝ 𝕣∗)
txout-preserves-value (step₁ {Rˢ = Rˢ}{𝕣∗}{λˢ = (α , Γ at t , _ at t′ , Γ→Γ′ , _ , R≈) , _} Rˢ~Rᶜ coh)
  with coh
... | [L] [1] {⟨G⟩C = ⟨G⟩C} _ ∃Γ≈ _ _ _
  = value-preserving⇒ (txout-preserves-value Rˢ~Rᶜ)
  where open H₁ (ℝ∗⇒ℝ 𝕣∗) t α t Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈
... | [L] [2] {⟨G⟩C = ⟨G⟩C} {A = A} {Δ×h̅ = Δ×h̅ } {k⃗ = k⃗} R≈ ∃Γ≈ as≡ All∉ Hon⇒ _ _ _ _ _
  = value-preserving⇒ (txout-preserves-value Rˢ~Rᶜ)
  where
    _Δ : List (Secret × Maybe ℕ)
    _Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

    sechash⁺ : (proj₁ $ unzip _Δ) ↦ ℤ
    sechash⁺ a∈ =
      let _ , a×m∈ , _    = ∈-unzip⁻ˡ _Δ a∈
          (_ , _ , z) , _ = L.Mem.∈-map⁻ (λ{ (s , mn , _) → s , mn }) a×m∈
      in z

    open H₂ (ℝ∗⇒ℝ 𝕣∗) t α t _ R≈ A A ⟨G⟩C _Δ sechash⁺ k⃗ Γ→Γ′ ∃Γ≈
-- T0D0: Typechecking case [6] hangs: figure out the correct level of abstraction.
-- ... | [L] [6] {c = c} {Γ₀ = Γ₀} {c′ = c′} {y′ = y′}
--               {ds = ds}{ss}{i} {v = v}{y}
--               t≡ d≡ R≈ ∃Γ≈ fresh-y′ p⟦Δ⟧≡ As≡∅
--   = value-preserving⇒ (txout-preserves-value Rˢ~Rᶜ)
--   where
--     open ∣SELECT c i
--     _Δ  = || map (uncurry₃ _∶_♯_) ss
--     Γ₂  = _Δ ∣ Γ₀

--     open H₆ (ℝ∗⇒ℝ 𝕣∗) t α t′ c v y ds Γ₂ c′ y′ R≈ Γ→Γ′ ∃Γ≈ using (module H₆′; Liftᶜ)

--     open H₆′ (
--       let
--         ⟨G⟩C″ , _ , _ , c⊆ , anc = ANCESTOR {R = Rˢ} {Γ = Γ} R≈ (here refl)
--         ⟨ G ⟩ C″ = ⟨G⟩C″

--         d∈ : d ∈ subtermsᵃ′ ⟨G⟩C″
--         d∈ = c⊆ (L.Mem.∈-lookup i)

--         T : ∃Tx
--         T = let _ , ∀d∗ = COMPILE (Liftᶜ anc)
--                 _ , Tᵈ = ∀d∗ d∈ :~ d≡ ⟪ ∃Txᶜ ⟫
--             in -, -, Tᵈ
--       in
--         T at 0F
--       )
... | [L] [18] _ ∃Γ≈
  = value-preserving⇒ (txout-preserves-value Rˢ~Rᶜ)
  where open H₁₈ (ℝ∗⇒ℝ 𝕣∗) t α t′ Γ R≈ Γ→Γ′ ∃Γ≈

txout-preserves-value _ = {!!}
{-
... | [L] [2]  R≈ ∃Γ≈ as≡ All∉ Hon⇒ ∃B h≡ h∈O unique-h h♯sechash = {!!}
... | [L] [3]  R≈ ∃Γ≈ committedA A∈per ∃B = {!!}
... | [L] [4]  R≈ ∃Γ≈ fresh-z = {!!}
... | [L] [5]  d≡ R≈ ∃Γ≈ = {!!}
... | [L] [6]  t≡ d≡ R≈ ∃Γ≈ fresh-y′ p⟦Δ⟧≡ As≡∅ = {!!}
... | [L] [7]  R≈ ∃Γ≈ fresh-ys ∃B ∃α a∈ ∃λ first-λᶜ = {!!}
... | [L] [8]  t≡ d≡ R≈ fresh-xs As≡∅ ∃Γ≈ = {!!}
... | [L] [9]  d≡ R≈ ∃Γ≈ frsg-x As≡∅ ∀≤t = {!!}
... | [L] [10] R≈ ∃Γ≈ ∃λ first-λᶜ = {!!}
... | [L] [11] R≈ ∃Γ≈ fresh-y = {!!}
... | [L] [12] R≈ ∃Γ≈ ∃λ first-λᶜ = {!!}
... | [L] [13] R≈ ∃Γ≈ fresh-ys = {!!}
... | [L] [14] R≈ ∃Γ≈ ∃λ first-λᶜ = {!!}
... | [L] [15] R≈ ∃Γ≈ fresh-y = {!!}
... | [R] [16] R≈ ∃Γ≈ fresh-y T ⊆ins T∈ first-λᶜ ¬coh = {!!}
... | [R] [17] R≈ ∃Γ≈ T ⊆ins ¬coh = {!!}
-}

-- _∈ᵤₜₓₒ_ : TxInput′ → Blockchain → Set
-- txi ∈ᵤₜₓₒ b = hashTxⁱ txi ∈ˢ UTXO b

-- lemma6 :
--     (R~ : Rˢ ~ Rᶜ) → let 𝕣 = R~ .proj₁ in
--     (c∈ : Rˢ ≈⋯ ⟨ c , v ⟩at x ⋯)
--     --————————————————————————
--   → (𝕣 ∙txoutC c∈) ∈ᵤₜₓₒ 𝔹 Rᶜ

-- lemma6 (𝕣 , base init R≈ cinit txout≡ sechash∅ κ∅) c∈
--   = ⊥-elim
--   $ Initial⇒∉ init
--   $ c∈ :~ R≈ ⟪ (λ ◆ → _ ∈ᶜ ◆ .end .cfg) ⟫

-- lemma6 (_ , step₁ {∃𝕣@(Rˢ , 𝕣)}{Γₜ}{Rᶜ}{λᶜ}{𝕒}{𝕣′} R~ coh) c∈
--   = {!!}

-- -- lemma6 {v = v} {x = x} {c = c} (𝕣 , step₂ {λᶜ} R~ coh) c∈
-- --   = let txi@((_ , _ , T) at o) , T∈ , ≡v , T♯≡ = lemma6 (𝕣 , R~) c∈
-- --     in  txi , {!∈-∪⁺ˡ (T ♯ at o) (UTXO txs ─ STXOₜₓ tx) (UTXOₜₓ tx) !} , ≡v , T♯≡
-- -- lemma6 {Rˢ}{Rᶜ = 𝕓@(.(submit T) ∷ ls)} {c = c} {v = v} {x = x}
-- --        (𝕣@(record{ txout′ = txout}) , step₂ {λᶜ = .(submit T)} R~ ([1] {T = T} ins♯)) c∈
-- --   = let txi@((_ , _ , T′) at o) = 𝕣 ∙txoutC c∈
-- --         T∈′ , ≡v , T♯≡ = lemma6 (𝕣 , R~) c∈
-- --         Tₒ′ = T′ ♯ at toℕ o

-- --         T∉ : Tₒ′ ∉ˢ STXOₜₓ T
-- --         T∉ x∈ =
-- --           let
-- --             x∈′ : Tₒ′ ∈ V.toList (T .proj₂ .proj₂ .inputs)
-- --             x∈′ = ∈ˢ-fromList⁻ x∈

-- --             Γ∈ : ⟨ c , v ⟩at x ∈ allCfgs Rˢ
-- --             Γ∈ = {!!}

-- --             txi′ : TxInput′
-- --             txi′ = Txout∈ txout {! end∈allCfgsᵗ !} (here refl)

-- --             Tₒ∈ : Tₒ′ ∈ (hashTxⁱ <$> codom txout)
-- --             Tₒ∈ = {!!}
-- --           in
-- --             ins♯ (x∈′ , Tₒ∈)

-- --         T∈ : Tₒ′ ∈ˢ UTXO (𝔹 𝕓)
-- --         T∈ = ∈-∪⁺ˡ Tₒ′ (UTXO (𝔹 ls) ─ STXOₜₓ T)
-- --                        (UTXOₜₓ T)
-- --                        (∈-─⁺ _ (UTXO $ 𝔹 ls) (STXOₜₓ T) T∈′ T∉)
-- --     in  txi , T∈ , ≡v , T♯≡


-- -- lemma6 (𝕣 , step₂ {λᶜ = .(A →O∶ m)}  R~ ([2] {A = A}{m} (inj₁ refl))) c∈ = lemma6 (𝕣 , R~) c∈
-- -- lemma6 (𝕣 , step₂ {λᶜ = .(O→ A ∶ m)} R~ ([2] {A = A}{m} (inj₂ refl))) c∈ = lemma6 (𝕣 , R~) c∈
-- -- lemma6 (𝕣 , step₂ {λᶜ = .(A →∗∶ m)}  R~ ([3] {A}{m} _))               c∈ = lemma6 (𝕣 , R~) c∈
