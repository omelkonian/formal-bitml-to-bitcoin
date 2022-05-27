-- {-# OPTIONS --allow-unsolved-metas #-}
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


open import Bitcoin using (KeyPair)

module SecureCompilation.Lemma6
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (d; α; Γ; Γ′; Γ″; Γₜ; Γₜ′; t; t′)
open import ComputationalModel Participant Honest finPart keypairs as C
  hiding (∣_∣; `; t; t′)
open import SecureCompilation.Compiler Participant Honest η
open import SecureCompilation.Coherence Participant Honest finPart keypairs η

-- ∃deposit : Blockchain → ℝ Rˢ → Rˢ ≈⋯ ⟨ c , v ⟩at x ⋯ → Set
-- ∃deposit {Rˢ}{c}{v} 𝕓 𝕣 c∈ =
--     -- There exists a transaction output (T, o)...
--   ∃ λ (txi : TxInput′) → let (_ , _ , T) at o = txi; Tₒ = T ♯ at toℕ o in
--         -- ...unspent in 𝕓...
--         (Tₒ ∈ˢ UTXO 𝕓)
--         -- ...with value v.
--       × ((T ‼ᵒ o) .proj₂ .value ≡ v)
--         -- Further, T is generated by...
--       × let
--           Γₜ = Rˢ .end
--           ⟨G⟩C , _ , ad∈ , c⊆ , anc = ANCESTOR {Rˢ}{c = c} {Γ = Γₜ .cfg} (≈ᵗ-refl {Γₜ}) c∈

--           K : 𝕂 (⟨G⟩C .G)
--           K {p} _ = K̂ p

--           vad , txout , sechash , κ = LIFTᶜ 𝕣 anc
--           -- ...invoking the compiler as...
--           T₀ , 𝕔 = bitml-compiler {ad = ⟨G⟩C} vad sechash txout K κ
--         in
--           -- ...the initial transaction...
--           (T ♯ ≡ T₀ .proj₂ ♯)
--           -- ...or retrieving the transaction for a specific subterm.
--         ⊎ ∃ λ (eq : length c ≡ V.length (T .outputs)) →
--           let
--             i : Index c
--             i = ⟪ Fin ⟫ eq ~: o

--             open ∣SELECT c i

--             ∃tx : ∃Txᶜ d∗
--             ∃tx = 𝕔 $ h-subᶜ {ds = ⟨G⟩C .C} $ c⊆ (L.Mem.∈-lookup i)
--           in
--             T ♯ ≡ ∃tx .proj₂ ♯

unquoteDecl _∙Value _∙value ∙value=_ = genAccessor _∙Value _∙value ∙value=_ (quote C.Value)
instance
  TxOutput∙Value : TxOutput ctx ∙Value
  TxOutput∙Value = ∙value= value

  ∃TxOutput∙Value : ∃TxOutput ∙Value
  ∃TxOutput∙Value = ∙value= λ where (_ , txo) → txo ∙value

  TxInput′∙Value : TxInput′ ∙Value
  TxInput′∙Value = ∙value= λ where ((_ , _ , T) at o) → (T ‼ᵒ o) ∙value

unquoteDecl _∙Run _∙run ∙run=_ = genAccessor _∙Run _∙run ∙run=_ (quote S.Run)
instance
   ℝˢ-has-Run : ℝˢ ∙Run
   ℝˢ-has-Run = ∙run= λ where (_⦊_ R {Γ} (𝕒 , _)) → Γ ∷ R ⊣ 𝕒

   ∃ℝ-has-Run : (∃ ℝ) ∙Run
   ∃ℝ-has-Run = ∙run= proj₁

   ℝˢ-has-ℝ : HasField′ ℝˢ (ℝ ∘ _∙run)
   ℝˢ-has-ℝ ._∙ (_ ⦊ _ , 𝕣) = 𝕣

-- TxoutC≡ : 𝕣 ∙txoutC

variable
  𝕣ˢ : ℝˢ
  𝕣ᶜ : ℝᶜ
  ∃𝕣 : ∃ ℝ

txout-preserves-value :
  (R~ : ∃𝕣 ~′ Rᶜ)
  (c∈ : ∃𝕣 ∙run ≈⋯ ⟨ c , v ⟩at x ⋯) →
  --—————————————————————————————————
  ((∃𝕣 .proj₂) ∙txoutC c∈) ∙value ≡ v

-- txout-preserves-value {𝕣ˢ}{𝕣ᶜ}{c}{v}{x} ([L] [1] {Rˢ}{⟨G⟩C}{Γ}{t}{𝕣 = 𝕣} R≈ ∃Γ≈ vad hon d⊆) c∈
--   = {!!}

-- txout-preserves-value {.(_ ⦊ _)} {.(_ ⦊ _)} {c} {v} {x} ([L] x₁) c∈ = {!x₁!}
txout-preserves-value
  {c = c} {v} {x}
  (step₁ {Rˢ = Rˢ}{Γₜ₀@(Γ₀ at t)}{Rᶜ}{λᶜ} {𝕒}{𝕣}{𝕔} -- {_λˢ@(𝕒 , _𝕣′)}
         Rˢ~Rᶜ
         ([L]_ {.Rˢ}{.Γₜ₀}{.Rᶜ}{.λᶜ}{.(𝕒 , ℝ∷ {R = Rˢ} {Γₜ = Γₜ₀} 𝕒 𝕔 𝕣)}
               ([1] {.Rˢ}{⟨G⟩C}{Γ}{.t}{𝕣 = .𝕣} R≈ ∃Γ≈ vad hon d⊆)))
  c∈
  = {!qed₀!} -- qed
  where
    -- 𝕣 = drop-ℝ 𝕒 𝕣′ -- _λˢ
    𝕣′ = ℝ∷ {R = Rˢ} {Γₜ = Γₜ₀} 𝕒 𝕔 𝕣
    -- _ : 𝕣 ≡ _𝕣
    -- _ = refl

    Γₜ  = Γ at t
    α   = advertise⦅ ⟨G⟩C ⦆
    Γ′  = ` ⟨G⟩C ∣ Γ
    t′  = t
    Γₜ′ = Γ′ at t′
    Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
    Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

    open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈
      hiding (λˢ; 𝕣′)
    -- 𝕣′ = λˢ .proj₂
    -- open Properties using (c∈⇐; txoutEndC≡)

    Γ″ = ∃Γ≈ .proj₁ -- : Cfg
    Γ≈ = ∃Γ≈ .proj₂ -- : Γ″ ≈ Γ′

    c∈Rˢ : Rˢ ≈⋯ ⟨ c , v ⟩at x ⋯
    -- c∈Rˢ = L.Perm.∈-resp-↭ Properties.namesʳ↭ (c∈⇒x∈ {Γ = R .end .cfg} c∈)
    c∈Rˢ = c∈⇐ c∈

    -- 𝕣ˢ′ = Rˢ ⦊ λˢ
    -- 𝕣′  = ℝˢ⇒ℝ 𝕣ˢ′
    -- _ : 𝕣ˢ′ ∙run ≈⋯ ⟨ c , v ⟩at x ⋯
    -- _ = c∈

    H : (𝕣 ∙txoutC c∈Rˢ) ∙value ≡ v
    H = txout-preserves-value Rˢ~Rᶜ c∈Rˢ

    eq : 𝕣 ∙txoutC c∈Rˢ ≡ 𝕣′ ∙txoutC c∈
    eq = sym $ txoutEndC≡ c∈

    -- _ : 𝕣′ ≡ _𝕣′
    -- _ = {!refl!}

    qed₀ : (𝕣′ ∙txoutC c∈) ∙value ≡ v
    qed₀ = subst (λ ◆ → ◆ ∙value ≡ v) eq H

    -- qed : (_𝕣′ ∙txoutC c∈) ∙value ≡ v
    -- qed = {!qed₀!}
txout-preserves-value _ _ = {!!}

{-
txout-preserves-value₁ {c = c}{v}{x} coh c∈
  -- = case coh of λ where
  --     ([L] [1]  R≈ ∃Γ≈ vad hon d) → txout-preserves-value₁ coh (there c∈)
  --     _ → ?
  with coh
... | [L] [1] {Rˢ}{⟨G⟩C}{Γ}{t}{𝕣 = 𝕣} R≈ ∃Γ≈ vad hon d⊆ = {!!} -- txout-preserves-value₁ coh c∈′
  where
    Γₜ  = Γ at t
    α   = advertise⦅ ⟨G⟩C ⦆
    Γ′  = ` ⟨G⟩C ∣ Γ
    t′  = t
    Γₜ′ = Γ′ at t′
    Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
    Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

    open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈
    𝕣ˢ = Rˢ ⦊ λˢ

    Γ″ = ∃Γ≈ .proj₁ -- : Cfg
    Γ≈ = ∃Γ≈ .proj₂ -- : Γ″ ≈ Γ′

    c∈Γ′ : ⟨ c , v ⟩at x ∈ᶜ Γ′
    c∈Γ′ = ∈ᶜ-++⁺ʳ (` ⟨G⟩C) Γ {!!}

    c∈Γ″ : ⟨ c , v ⟩at x ∈ᶜ Γ″
    -- c∈Γ″ = ∈ᶜ-resp-≈ {Γ′}{Γ″} (↭-sym Γ≈) c∈Γ′
    c∈Γ″ = c∈

    c∈′ : 𝕣ˢ ∙run ≈⋯ ⟨ c , v ⟩at x ⋯
    c∈′ = c∈Γ″

    qed : ((𝕣ˢ ∙) ∙txoutC c∈) ∙value ≡ v
    qed = ?
... | _ = {!!}
-}
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
... | [L] [18] δ>0 ∃Γ≈ = {!!}
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
