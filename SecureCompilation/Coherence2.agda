open import Prelude.Init hiding (T)
open L.Mem
open import Prelude.Lists
open import Prelude.General
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Collections
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Ord
open import Prelude.ToN
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.Setoid

open import Bitcoin.Crypto using (KeyPair)

module SecureCompilation.Coherence2
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel2 Participant Honest as S
  hiding (_∎; begin_)

open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
  hiding (Hon; Initial; Valid; Σ)
open import Bitcoin as C
  hiding (t; t′; `; ∣_∣; ∙)

open import SecureCompilation.Compiler Participant Honest η

private
  variable
    ⟨G⟩C ⟨G⟩C′ ⟨G⟩C″ : Advertisement
    T T′ : ∃Tx

    -- Rˢ : S.Run
    𝕣  : ℝ Rˢ

    ∃𝕣 ∃𝕣′ : ∃ ℝ

postulate
  encode : Txout Rˢ → Advertisement → Message
  -- ^ encode {G}C as a bitstring, representing each x in it as txout(x)

  SIGᵖ : ∀ {A : Set} → ℤ {- public key -} → A → ℤ

  ∣_∣ᶻ : ℤ → ℕ
  ∣_∣ᵐ : Message → ℕ

_-redeemableWith-_ : S.Value → KeyPair → ∃TxOutput
v -redeemableWith- k = Ctx 1 , record {value = v;  validator = ƛ (versig [ k ] [ # 0 ])}

-- T0D0: redefine Message ≈ ℤ ??
SIGᵐ : KeyPair → Message → Message
SIGᵐ k = map (SIG k)

-- ** Types and notation.
data coher : ∃ ℝ → C.Run → Set

data coher₂ (Rˢ : S.Run) (txout : Txout Rˢ) : C.Label → Set

data coher₁ :
  (Rˢ : S.Run) (Γₜ : Cfgᵗ) (𝕒 : 𝔸 Rˢ Γₜ)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  → ℝ Rˢ
  → ℝ (Γₜ ∷ Rˢ ⊣ 𝕒)
  → Set

data coher₁₁ :
  (Rˢ : S.Run) (Γₜ : Cfgᵗ) (𝕒 : 𝔸 Rˢ Γₜ)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  → ℝ Rˢ
  → ℝ (Γₜ ∷ Rˢ ⊣ 𝕒)
  → Set

data coher₁₂ :
  (Rˢ : S.Run) (Γₜ : Cfgᵗ) (𝕒 : 𝔸 Rˢ Γₜ)
  (Rᶜ : C.Run) (λᶜ : C.Label)
  → ℝ Rˢ
  → ℝ (Γₜ ∷ Rˢ ⊣ 𝕒)
  → Set

data coher where

  base : let Rˢ , 𝕣 = ∃𝕣; open ℝ 𝕣 in

      -- (i) Rˢ = Γ₀ ∣ 0, with Γ₀ initial
      (init : Initial Γ₀)
    → (cfg≡ : Rˢ ≡ ((Γ₀ at 0) ∎⊣ (init , refl)))
      -- (ii) Rᶜ = T₀ ⋯ initial
    → (cinit : C.Initial Rᶜ)
    → let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in

      -- (iii) generation of public keys, we do not consider that here
      -- [T0D0] is our idealistic assumption reasonable?? -- ask BitML authors

      -- (iv) txout { ⟨ A , v ⟩ₓ ∈ Γ₀ ↦ T₀{value = $ v, spendable with K̂(A)(rₐ)} ∈ T₀ }
      (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀)
         → ∃ λ oᵢ
         → let
             x∈ : x ∈ namesʳ Rˢ
             x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) $ deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈
           in
             (txout′ x∈ ≡ ∃T₀ at oᵢ) × (T₀ ‼ᵒ oᵢ ≡ v -redeemableWith- K̂ A)
      )
      -- (v) dom sechash = ∅
    → dom sechash′ ≡ []
      -- (vi) dom κ = ∅
    → dom κ′ ≡ []
      --——————————————————————————————————————————————————————————————————————
    → coher (Rˢ , 𝕣) Rᶜ

  step₁ : let Rˢ , 𝕣 = ∃𝕣 in
        ∀ {𝕒 : 𝔸 Rˢ Γₜ} →
          let Rˢ′ = Γₜ ∷ Rˢ ⊣ 𝕒 in
        ∀ {𝕣′ : ℝ Rˢ′} →

      coher ∃𝕣 Rᶜ
    → coher₁ Rˢ Γₜ 𝕒 Rᶜ λᶜ 𝕣 𝕣′
      --——————————————————————————————————————————————————————————————————————
    → coher ∃𝕣′ (λᶜ ∷ Rᶜ)

  step₂ : let Rˢ , 𝕣 = ∃𝕣; open ℝ 𝕣 in

      coher ∃𝕣 Rᶜ
    → coher₂ Rˢ txout′ λᶜ
      ----------------------------------------
    → coher ∃𝕣 (λᶜ ∷ Rᶜ)

_~_ _≁_ : S.Run → C.Run → Set
Rˢ ~ Rᶜ = ∃[ 𝕣 ] coher (Rˢ , 𝕣) Rᶜ
Rˢ ≁ Rᶜ = ¬ Rˢ ~ Rᶜ
-- = ∃ (∃ (∃ (coher Rˢ Rᶜ)))
-- [BUG] not inferring type of existentials, although dependency is evident

-- ** Definitions.
data coher₁ where
  [L] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} {𝕒 : 𝔸 Rˢ Γₜ} → let Rˢ′ = Γₜ ∷ Rˢ ⊣ 𝕒 in
        ∀ {𝕣′ : ℝ Rˢ′}
    → coher₁₁ Rˢ Γₜ 𝕒 Rᶜ λᶜ 𝕣 𝕣′
    → coher₁  Rˢ Γₜ 𝕒 Rᶜ λᶜ 𝕣 𝕣′

  [R] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} {𝕒 : 𝔸 Rˢ Γₜ} → let Rˢ′ = Γₜ ∷ Rˢ ⊣ 𝕒 in
        ∀ {𝕣′ : ℝ Rˢ′}
    → coher₁₂ Rˢ Γₜ 𝕒 Rᶜ λᶜ 𝕣 𝕣′
    → coher₁  Rˢ Γₜ 𝕒 Rᶜ λᶜ 𝕣 𝕣′

data coher₁₁ where

  -- ** Advertising a contract
  [1] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} →
      let
        open ℝ 𝕣
        ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G
        Γₜ = Γ at t
      in
      (cfg≈ : Rˢ ≈⋯ Γₜ) (Γ′≈  →
      let
        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        α   = advertise⦅ ⟨G⟩C ⦆
        Γ′  = ` ⟨G⟩C ∣ Γ
        t′  = t
        Γₜ′ = Γ′ at t′
        λᶜ  = A →∗∶ C
      in
      -- Hypotheses from [C-Advertise]
        (vad : Valid ⟨G⟩C)
      → (hon : Any (_∈ Hon) (participants G))
      → (d⊆  : deposits ⟨G⟩C ⊆ deposits Γ)
      →
      let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

        𝕒 : 𝔸 Rˢ Γₜ′
        𝕒 = α , (Γₜ , (Γₜ′ , (Γ→Γ′ , (≈ᵗ-refl {Γₜ′} , cfg≈))))

        -- txout′ = txout, sechash′ = sechash, κ′ = κ
        open H₁ {Rˢ} 𝕣 t α t′ Γ cfg≈ ⟨G⟩C Γ→Γ′
      in
      --——————————————————————————————————————————————————————————————————————
      coher₁₁ Rˢ Γₜ′ 𝕒 Rᶜ λᶜ 𝕣 𝕣′

{-
  -- ** Stipulation: committing secrets
  [2] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
      ∀ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
        -- [BUG] doesnt work with t/Γ₀/⟨G⟩C as generalized variables
        {t Γ₀ ⟨G⟩C} {k⃗ : 𝕂²′ ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C; Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in

      -- T0D0: Γᵣₛ does not necessary keep ⟨G⟩C in its head, replace _≡_ with _≈_?
      (cfg≡ : Rˢ ≡⋯ Γₜ)
    → let
        C : Message
        C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

        Δ : List (Secret × Maybe ℕ)
        Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

        (as , ms) = unzip Δ

        Δᶜ : Cfg
        Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ

        h̅ : List ℤ -- ≈ Message
        h̅ = map (proj₂ ∘ proj₂) Δ×h̅

        k̅ : List ℤ -- ≈ Message
        k̅ = concatMap (map pub ∘ codom) (codom k⃗)

        C,h̅,k̅ : Message
        C,h̅,k̅ = C ◇ h̅ ◇ k̅

        C,h̅,k̅ₐ : Message
        C,h̅,k̅ₐ = SIGᵐ (K A) C,h̅,k̅

        α   = auth-commit⦅ A , ⟨G⟩C , Δ ⦆
        Γ′  = Γ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
        t′  = t
        Γₜ′ = Γ′ at t′
        λᶜ  = B →∗∶ C,h̅,k̅ₐ
      in
      -- Hypotheses from [C-AuthCommit]
      (as≡ : as ≡ secretsOfᵖ A G)
      (All∉ : All (_∉ secretsOfᶜᶠ A Γ₀) as)
      (Hon⇒ : A ∈ Hon → All Is-just ms) →
      let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthCommit] as≡ All∉ Hon⇒) refl

        -- (v) txout = txout′ (vi) extend sechash′ (vii) extend κ′
        sechash⁺ : as ↦ ℤ
        sechash⁺ a∈ =
          let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
              (_ , _ , z) , _ = ∈-map⁻ (λ{ (s , mn , _) → s , mn }) a×m∈
          in z

        open H₂ {Rˢ} 𝕣 t α t′ Γ cfg≡ A A ⟨G⟩C Δ sechash⁺ k⃗ Γ→Γ′

        𝕒 : 𝔸 Rˢ Γₜ′
        𝕒 = α , Γₜ , Γₜ′ , Γ→Γ′ , ({!refl!} , {!↭-refl!}) , {!case cfg≡ of λ{ refl → refl , ↭-refl }!}
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
    → coher₁₁ Rˢ Γₜ′ 𝕒 Rᶜ λᶜ 𝕣 𝕣′
-}

--   -- ** Stipulation: authorizing deposits
--   [3] : ∀ {⟨G⟩C : Advertisement} {vad : Valid ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G in
--         ∀ {t A Γ₀} → let Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = auth-init⦅ A , ⟨G⟩C , x ⦆
--         Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
--         t′  = t
--         Γₜ′ = Γ′ at t′
--       in
--       -- Hypotheses from [C-AuthInit]
--       (committedA : partG ⊆ committedParticipants Γ₀ ⟨G⟩C)
--       (A∈per : (A , v , x) ∈ persistentDeposits G)

--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙ from the hypotheses of [C-Advertise]
--       --       ∘ which introduces ` ⟨G⟩C
--       --       ⇒ deposits ⟨G⟩C ⊆ deposits Γ₀
--       --       ⇒ namesʳ ⟨G⟩C ⊆ namesʳ Γ₀
--       --   ∙ from the hypotheses of [C-AuthCommit]
--       --       ∘ which introduces ⟨ Aᵢ ∶ aᵢ ♯ Nᵢ ⟩
--       --       ⇒ secrets ⟨G⟩C ⊆ secrets Γ₀
--       --       ⇒ namesˡ ⟨G⟩C ⊆ namesˡ Γ₀
--       (names⊆ : G ⊆⟨on:names⟩ Γ₀)
--       --   ∙ from the hypotheses of [C-Advertise]
--       --       ∘ which introduces ` ⟨G⟩C
--       --       ⇒ ∃(p ∈ partG). p ∈ Hon
--       --   ∙ from the hypotheses of [C-AuthCommit]
--       --       ∘ which introduces ⟨ Aᵢ ∶ aᵢ ♯ Nᵢ ⟩ and Aᵢ auth⦅ ♯▷ ad ⦆
--       --       ⇒ we know at least one participant Aᵢ is honest
--       --       → therefore, ad ∈ authorizedHonAds Γ₀
--       (ad∈₀ : ⟨G⟩C ∈ authorizedHonAds Γ₀) →

--       let
--         A∈′ : A ∈ committedParticipants Γ₀ ⟨G⟩C
--         A∈′ = committedA $ ∈-nub⁺ (persistentParticipants⊆ {g = G} $ ∈-map⁺ proj₁ A∈per)

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

--         -- (iv) txout = txout′, sechash = sechash′, κ = κ′
--         open H₃ {R = Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x cfg≡ Γ→Γ′

--         Tᵢₙᵢₜ : ∃Tx
--         Tᵢₙᵢₜ =
--           let -- invoke compiler
--             K : 𝕂 G
--             K {p} _ = K̂ p

--             open H₃′ ad∈₀ names⊆

--             ∃tx¹ , _ = bitml-compiler {ad = ⟨G⟩C} vad sechash₀ txout₀ K κ₀
--           in
--             -, -, proj₂ ∃tx¹

--         -- (i) broadcast Tᵢₙᵢₜ , signed with A's private key
--         m = [ SIG (K̂ A) Tᵢₙᵢₜ ]
--         λᶜ = B →∗∶ m
--       in
--       -- (ii) Tᵢₙᵢₜ occurs as a message in Rᶜ
--       (∃ λ B → (B →∗∶ [ HASH Tᵢₙᵢₜ ]) ∈ Rᶜ)

--       -- (iii) broadcast message in Rᶜ
--       -- T0D0: make sure that λᶜ is the first occurrence of such a message after Tinit in Rᶜ
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′


--   -- ** Stipulation: activating the contract
--   [4] : ∀ {t Γ₀ G C}
--     → let
--         ad      = ⟨ G ⟩ C
--         toSpend = persistentDeposits G
--         partG   = nub-participants G
--         v       = sum $ map (proj₁ ∘ proj₂) toSpend

--         Γ = ` ad ∣ Γ₀
--           ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ] }) toSpend
--           ∣ || map (_auth[ ♯▷ ad ]) partG
--         Γₜ = Γ at t
--       in
--       {vad : Valid ad}
--       -- (i) consume {G}C and its persistent deposits from Rˢ
--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙ from the hypotheses of [C-Advertise]
--       --       ∘ which introduces ` ⟨G⟩C
--       --       ⇒ deposits ⟨G⟩C ⊆ deposits Γ₀
--       --       ⇒ namesʳ ⟨G⟩C ⊆ namesʳ Γ₀ ⊆ namesʳ (_ ∣ Γ₀ ∣ _)
--       --   ∙ from the hypotheses of [C-AuthCommit]
--       --       ∘ which introduces ⟨ Aᵢ ∶ aᵢ ♯ Nᵢ ⟩
--       --       ⇒ secrets ⟨G⟩C ⊆ secrets Γ₀
--       --       ⇒ namesˡ ⟨G⟩C ⊆ namesˡ Γ₀
--     → (names⊆ : G ⊆⟨on:names⟩ Γ₀)

--       -- [T0D0] additional hypothesis, should hold from the hypotheses of [C-Advertise]
--     → (honG : Any (_∈ Hon) partG)

--     → let
--         α   = init⦅ G , C ⦆
--         Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [C-Init] refl

--         open H₄ {R = Rˢ} 𝕣 t α t′ ad Γ₀ toSpend partG v z cfg≡ Γ→Γ′

--         Tᵢₙᵢₜ : ∃Tx
--         Tᵢₙᵢₜ =
--           let -- invoke compiler
--             K̂ : 𝕂 G
--             K̂ {p} _ = K̂ p

--             open H₄′ honG names⊆

--             ∃tx¹ , _ = bitml-compiler {ad = ad} vad sechash₀ txout₀ K̂ κ₀
--           in
--             -, -, proj₂ ∃tx¹

--         -- (ii) append Tᵢₙᵢₜ to the blockchain
--         λᶜ = submit Tᵢₙᵢₜ

--         -- (iii) sechash = sechash′, κ = κ′, txout extends txout′ with (z ↦ Tᵢₙᵢₜ)
--         open H₄″ (Tᵢₙᵢₜ at 0F)
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′


--   -- ** Contract actions: authorize control
--   [5] : let open ℝ 𝕣 in
--       ∀ {⟨G⟩C : Advertisement} {vad : Valid ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in
--       ∀ {v x Γ₀ t c′} {i : Index c′} → let d = c′ ‼ i; d∗ = removeTopDecorations d in
--       let Γ = ⟨ c′ , v ⟩at x ∣ Γ₀; Γₜ = Γ at t in

--       -- D ≡ A ∶ D′
--       (D≡A:D′ : A ∈ authDecorations d)

--       -- (i) Rˢ contains ⟨C′ , v⟩ₓ with C′ = D + ∑ᵢ Dᵢ

--     → (cfg≡ : Rˢ ≡⋯ Γₜ)

--       -- (ii) {G}C is the ancestor of ⟨C′, v⟩ₓ in Rˢ
--     → (anc : Ancestor Rˢ (c′ , v , x) ⟨G⟩C)
--     → let d⊆ , ad∈ , _ = anc

--           d∈ : d ∈ subtermsᶜ′ C
--           d∈ = d⊆ (∈-lookup i)
--       in

--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙  ...
--       (names⊆ : G ⊆⟨on:names⟩ Γ₀)

--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙  ...
--     → (A∈ : A ∈ partG)

--     → let
--         α   = auth-control⦅ A , x ▷ d ⦆
--         Γ′  = ⟨ c′ , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′
--       in
--       -- Hypotheses from [C-AuthControl], already in hypothesis `D≡A:D′`
--       let
--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

--         -- (iv) txout = txout′, sechash = sechash′, κ = κ′
--         open H₅ {R = Rˢ} 𝕣 t α t′ c′ v x Γ₀ A i cfg≡ Γ→Γ′

--         -- (iii) broadcast transaction T, as obtained from the compiler, signed by A
--         --       where ∙ (T′,o) = txout′(x)
--         --             ∙ T is the first transaction in Bd(d,d,T′,o,v,partG,0)
--         --       i.e. the one corresponding to subterm `d∗ = removeTopDecorations d`
--         T : ∃Tx
--         T =
--           let -- invoke compiler
--             K̂ : 𝕂 G
--             K̂ {p} _ = K̂ p

--             open H₅′ ⟨G⟩C ad∈ names⊆

--             -- retrieve transaction for specific subterm
--             d∗∈ : d∗ ∈ subtermsᵃ⁺ ⟨G⟩C
--             d∗∈ = h-subᶜ {ds = C} d∈

--             ∃tx¹ = proj₂ (bitml-compiler {ad = ⟨G⟩C} vad sechash₀ txout₀ K̂ κ₀) d∗∈
--           in
--             -, -, proj₂ ∃tx¹

--         λᶜ = B →∗∶ [ SIGᵖ (pub $ κ′ ad∈ d∈ {A} A∈) T ]
--       in
--       -- (v) transaction T has been previously broadcasted in Rᶜ, and λᶜ is the first signature on T after that
--       (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ T ♯ ]) Rᶜ)
--     → All (λ l → ¬ ∃ λ B → ¬ ∃ λ k → l ≡ B →∗∶ [ SIGᵖ k T ]) (Any-tail ∃λ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Contract actions: put
--   [6] : ∀ {⟨G⟩C″ : Advertisement} {vad : Valid ⟨G⟩C″} → let ⟨ G ⟩ C″ = ⟨G⟩C″; partG = nub-participants G in
--         -- [T0D0] should we *derive* that ⟨G⟩C is valid??
--         ∀ {ds : List (Participant × S.Value × Id)} {ss : List (Participant × Secret × ℕ)}
--           {i : Index c} → let d = c ‼ i; d∗ = removeTopDecorations d; As , ts = decorations d in

--       let
--         -- (i) xs = x₁⋯xₖ
--         (_ , vs , xs) = unzip₃ ds
--         (_ , as , _)  = unzip₃ ss
--         Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
--         Δ  = || map (λ{ (Bi , ai , Ni) → Bi ∶ ai ♯ Ni       }) ss
--         Γ₂ = Δ ∣ Γ₀
--         Γ  = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₂)
--         Γₜ = Γ at t
--       in
--       -- ii) in Rˢ, α consumes ⟨D+C,v⟩y and the deposits ⟨Aᵢ,vᵢ⟩ₓᵢ to produce ⟨C′,v′⟩y′
--       --     where D = ⋯ : put⋯reveal⋯.C′
--       --     let t be the maximum deadline in an after in front of D
--       --     T0D0: what should t′ be in case there are not after decorations?
--       (d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′)
--     → (cfg≡ : Rˢ ≡⋯ Γₜ)

--       -- (iii) {G}C″ is the ancestor of ⟨D+C,v⟩y in Rˢ
--     → (anc : Ancestor Rˢ (c , v , y) ⟨G⟩C″)
--     → let
--         d⊆ , ad∈ , _ = anc

--         d∈ : d ∈ subtermsᶜ′ C″
--         d∈ = d⊆ (∈-lookup i)
--       in
--       -- hypotheses from [C-PutRev]
--       (p⟦Δ⟧≡ : ⟦ p ⟧ Δ ≡ just true)
--       -- hypotheses from [Timeout]
--       (As≡∅ : As ≡ [])
--       -- (∀≤t : All (_≤ t) ts)
--       (t≡ : t ≡ maximum t ts)
--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙  ...
--       (names⊆ : G ⊆⟨on:names⟩ Γ₂) →
--       let
--         α   = put⦅ xs , as , y ⦆
--         Γ′  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         ∀≤t : All (_≤ t′) ts
--         ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Timeout] As≡∅ ∀≤t
--                  (⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡ ~: [C-PutRev] {ds = ds} {ss = ss} p⟦Δ⟧≡) refl

--         open H₆ {R = Rˢ} 𝕣 t α t′ c v y ds Γ₂ c′ y′ cfg≡ Γ→Γ′

--         -- (iv) submit transaction T
--         --      where ∙ (T′,o) = txout′(y)
--         --            ∙ T is the first transaction in Bc(c′,d,T′,o,v′,x⃗,partG,t)
--         --      i.e. the one corresponding to subterm `d∗ = put xs &reveal as if p → c′`
--         T : ∃Tx
--         T =
--           let -- invoke compiler
--             K : 𝕂 G
--             K {p} _ = K̂ p

--             open H₆″ ⟨G⟩C″ ad∈ names⊆

--             -- retrieve transaction for specific subterm
--             d∗∈ : d∗ ∈ subtermsᶜ⁺ C″
--             d∗∈ = h-subᶜ {ds = C″} d∈

--             ∃tx : ∃Txᶜ d∗
--             ∃tx = proj₂ (bitml-compiler {ad = ⟨G⟩C″} vad sechash₀ txout₀ K κ₀) d∗∈

--             ∃tx¹ : ∃Tx¹
--             ∃tx¹ = ∃tx :~ d≡ ⟪ ∃Txᶜ ⟫
--           in
--             -, -, proj₂ ∃tx¹

--         λᶜ = submit T

--         -- (v) extend txout′ with {y′↦(T,0)}, sechash = sechash′, κ = κ′
--         open H₆′ (T at 0F)
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Contract actions: authorize reveal
--   [7] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--       ∀ {a n} → let Γ = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀; Γₜ = Γ at t in
--       ∀ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C in

--       ∣ m ∣ᵐ ≤ η
--     → (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = auth-rev⦅ A , a ⦆
--         Γ′  = A ∶ a ♯ n ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [C-AuthRev] refl

--         C : Message
--         C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

--         Δ : List (Secret × Maybe ℕ)
--         Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

--         h̅ : Message
--         h̅ = map (proj₂ ∘ proj₂) Δ×h̅

--         k̅ : Message
--         k̅ = concatMap (map pub ∘ codom) (codom k⃗)

--         a∈ : a ∈ namesˡ Rˢ
--         a∈ = subst (λ ◆ → a ∈ namesˡ ◆) (sym cfg≡) $ ∈-++⁺ˡ {xs = namesˡ $ A ∶ a ♯ n} (here refl)

--         -- T0D0: should we search for a signature of this message instead?
--         C,h̅,k̅ : Message
--         C,h̅,k̅ = C ◇ h̅ ◇ k̅

--         -- (i) some participant B broadcasts message m
--         λᶜ = B →∗∶ m

--         -- (iii) txout = txout′, sechash = sechash′, κ = κ′
--         open H₇ {R = Rˢ} 𝕣 t α t′ A a n Γ₀ cfg≡ Γ→Γ′
--       in
--       -- (ii) in Rᶜ we find ⋯ (B → O ∶ m) (O → B : sechash′(a)) for some B ⋯
--       (∃ λ B → (B , m , [ sechash′ {a} a∈ ]) ∈ oracleInteractions Rᶜ)

--       -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
--     → (∃α : auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labels Rˢ)
--     → a ∈ namesˡ G

--       -- ... with a corresponding broadcast of m′=(C,h̅,k̅) in Rᶜ
--     → (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) Rᶜ)

--       -- (v) λᶜ is the first broadcast of m after the first broadcast of m′
--     → All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail ∃λ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Contract actions: split
--   [8] : ∀ {⟨G⟩C′ : Advertisement} {vad : Valid ⟨G⟩C′} → let ⟨ G ⟩ C′ = ⟨G⟩C′; partG = nub-participants G in
--         ∀ {i : Index c} → let d = c ‼ i; d∗ = removeTopDecorations d; As , ts = decorations d in
--         ∀ {vcis : List (S.Value × Contracts × Id)} → let vs , cs , xs = unzip₃ vcis; v = sum vs in
--         ∀ {t} → let Γ = ⟨ c , v ⟩at y ∣ Γ₀; Γₜ = Γ at t in

--       -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨C₀,v₀⟩ₓ₀ | ⋯ | ⟨Cₖ,vₖ⟩ₓₖ
--       --     where D = ⋯ : split vs → cs
--       --     let t be the maximum deadline in an after in front of D
--       --     T0D0: what should t′ be in case there are not after decorations?
--       (d≡ : d ≡⋯∶ split (zip vs cs))
--     → (cfg≡ : Rˢ ≡⋯ Γₜ)

--       -- (iii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
--     → (anc : Ancestor Rˢ (c , v , y) ⟨G⟩C′)
--     → let d⊆ , ad∈ , _ = anc

--           d∈ : d ∈ subtermsᶜ′ C′
--           d∈ = d⊆ (∈-lookup i)
--       in
--       -- hypotheses from [Timeout]
--       (As≡∅ : As ≡ [])
--       -- (∀≤t : All (_≤ t) ts)
--       (t≡ : t ≡ maximum t ts)
--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙  ...
--       (names⊆ : G ⊆⟨on:names⟩ Γ₀)

--     → let
--         α   = split⦅ y ⦆
--         Γ′  = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         ∀≤t : All (_≤ t′) ts
--         ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Timeout] As≡∅ ∀≤t (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Split] {vcis = vcis}) refl

--         open H₈ {R = Rˢ} 𝕣 t α t′ c v y Γ₀ vcis cfg≡ Γ→Γ′

--         -- (iii) submit transaction T
--         --       where ∙ (T′,o) = txout′(y)
--         --             ∙ T is the first transaction in Bpar(cs,d,T′,o,partG,t)
--         --       i.e. the one corresponding to subterm `d∗ = split (zip vs cs)`
--         T : ∃ λ i → Tx i (length xs)
--         T =
--           let -- invoke compiler
--             K : 𝕂 G
--             K {p} _ = K̂ p

--             open H₈″ ⟨G⟩C′ ad∈ names⊆

--             -- retrieve transaction for specific subterm
--             d∗∈ : d∗ ∈ subtermsᶜ⁺ C′
--             d∗∈ = h-subᶜ {ds = C′} d∈

--             ∃tx : ∃Txᶜ d∗
--             ∃tx = proj₂ (bitml-compiler {ad = ⟨G⟩C′} vad sechash₀ txout₀ K κ₀) d∗∈

--             ∃tx′ : ∃[ i ] Tx i (length $ zip vs cs)
--             ∃tx′ = ∃tx :~ d≡ ⟪ ∃Txᶜ ⟫

--             open ≡-Reasoning
--             vs≡ , cs≡ , xs≡ = length-unzip₃ vcis

--             l≡ : length xs ≡ length (zip vs cs)
--             l≡ = sym
--                $ begin length (zip vs cs)    ≡⟨ L.length-zipWith _,_ vs cs ⟩
--                        length vs ⊓ length cs ≡⟨ Nat.m≥n⇒m⊓n≡n $ Nat.≤-reflexive $ trans cs≡ (sym vs≡) ⟩
--                        length cs             ≡⟨ cs≡ ⟩
--                        length vcis           ≡⟨ sym xs≡ ⟩
--                        length xs             ∎

--             ∃tx″ : ∃[ i ] Tx i (length xs)
--             ∃tx″ = ⟪ (λ ◆ → ∃[ i ] Tx i ◆) ⟫ l≡ ~: ∃tx′
--           in
--             ∃tx″

--         ∃T = -, -, proj₂ T

--         λᶜ = submit ∃T

--         -- (iv) extend txout′ with {xᵢ ↦ (T,i)}, sechash = sechash′, κ = κ′
--         txout⁺ : xs ↦ TxInput′
--         txout⁺ x∈ = ∃T at (L.Any.index x∈)

--         open H₈′ txout⁺
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Contract actions: withdraw
--   [9] : ∀ {⟨G⟩C′ : Advertisement} {vad : Valid ⟨G⟩C′} → let ⟨ G ⟩ C′ = ⟨G⟩C′; partG = nub-participants G in
--         ∀ {i : Index c} → let d = c ‼ i; d∗ = removeTopDecorations d; As , ts = decorations d in
--         let Γ = ⟨ c , v ⟩at y ∣ Γ₀; Γₜ = Γ at t in

--       -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨A,v⟩ₓ (where D = ⋯ : withdraw A)
--       (d≡ : d ≡⋯∶ withdraw A)
--     → (cfg≡ : Rˢ ≡⋯ Γₜ)

--       -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
--     → (anc : Ancestor Rˢ (c , v , y) ⟨G⟩C′)
--     → let d⊆ , ad∈ , _ = anc

--           d∈ : d ∈ subtermsᶜ′ C′
--           d∈ = d⊆ (∈-lookup i)
--       in
--       -- hypotheses from [Timeout]
--       (As≡∅ : As ≡ [])
--       (∀≤t : All (_≤ t) ts)
--       -- [T0D0] additional hypotheses, should hold since we know the following:
--       --   ∙  ...
--       (names⊆ : G ⊆⟨on:names⟩ Γ₀)

--     → let
--         α   = withdraw⦅ A , v , y ⦆
--         Γ′  = ⟨ A has v ⟩at x ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Timeout] As≡∅ ∀≤t (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw]) refl

--         open H₉ {R = Rˢ} 𝕣 t α t′ c v y Γ₀ A x cfg≡ Γ→Γ′

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
--             K : 𝕂 G
--             K {p} _ = K̂ p

--             open H₉″ ⟨G⟩C′ ad∈ names⊆

--             -- retrieve transaction for specific subterm
--             d∗∈ : d∗ ∈ subtermsᶜ⁺ C′
--             d∗∈ = h-subᶜ {ds = C′} d∈

--             ∃tx : ∃Txᶜ d∗
--             ∃tx = proj₂ (bitml-compiler {ad = ⟨G⟩C′} vad sechash₀ txout₀ K κ₀) d∗∈

--             ∃tx¹ : ∃Tx¹
--             ∃tx¹ = ∃tx :~ d≡ ⟪ ∃Txᶜ ⟫
--           in
--             -, -, proj₂ ∃tx¹

--         λᶜ = submit T

--         -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
--         open H₉′ (T at 0F)
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: authorize join
--   [10] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--        ∀ {x x′ : Id} → let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = auth-join⦅ A , x ↔ x′ ⦆
--         Γ′  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-AuthJoin] refl

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) (here refl)

--         x′∈ : x′ ∈ namesʳ Rˢ
--         x′∈ = subst (λ ◆ → x′ ∈ namesʳ ◆) (sym cfg≡) (there (here refl))
--       in
--       (∃λ : Any (λ l → ∃ λ B → ∃ λ T
--                 → (l ≡ B →∗∶ [ T ♯ ])
--                 × (inputs  T ≡ hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x′∈) ∷ [])
--                 × (outputs T ≡ V.[ Ctx 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
--                 ) Rᶜ)
--     → let
--         T : ∃Tx
--         T = 2 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

--         -- (iii) broadcast transaction T, signed by A
--         m′ = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m′

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₀ {R = Rˢ} 𝕣 t α t′ A v x v′ x′ Γ₀ cfg≡ Γ→Γ′
--       in
--       -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: join
--   [11] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--        ∀ {x x′ : Id} → let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = join⦅ x ↔ x′ ⦆
--         Γ′  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-Join] refl

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) (here refl)

--         x′∈ : x′ ∈ namesʳ Rˢ
--         x′∈ = subst (λ ◆ → x′ ∈ namesʳ ◆) (sym cfg≡) (there (here refl))

--         -- (ii) submit transaction T
--         T : ∃Tx
--         T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
--            { inputs  = hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x′∈) ∷ []
--            ; wit     = wit⊥
--            ; relLock = V.replicate 0
--            ; outputs = V.[ (v + v′) -redeemableWith- K̂ A ]
--            ; absLock = 0 }
--         λᶜ = submit T

--         -- (iii) extend txout′ with y↦T₀ (removing {x↦_;x′↦_}), sechash = sechash′, κ = κ′
--         open H₁₁ {R = Rˢ} 𝕣 t α t′ A v x v′ x′ y Γ₀ cfg≡ (T at 0F) Γ→Γ′
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: authorize divide (similar to [10])
--   [12] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--        ∀ {x : Id} → let Γ = ⟨ A has (v + v′) ⟩at x ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = auth-divide⦅ A , x ▷ v , v′ ⦆
--         Γ′  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-AuthDivide] refl

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) (here refl)
--       in
--       (∃λ : Any (λ l → ∃ λ B → ∃ λ T
--                 → (l ≡ B →∗∶ [ T ♯ ])
--                 × (inputs  T ≡ V.[ hashTxⁱ (txout′ {x} x∈) ])
--                 × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
--                 ) Rᶜ)
--     → let
--         T : ∃Tx
--         T = 1 , 2 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

--         -- (iii) broadcast transaction T, signed by A
--         m′ = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m′

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₂ {R = Rˢ} 𝕣 t α t′ A v v′ x Γ₀ cfg≡ Γ→Γ′
--       in
--       -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: divide (dimilar to [11])
--   [13] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--        ∀ {x : Id} → let Γ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = divide⦅ x ▷ v , v′ ⦆
--         Γ′  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-Divide] refl

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) (here refl)

--         -- (iii) submit transaction T
--         T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
--            { inputs  = V.[ hashTxⁱ (txout′ {x} x∈) ]
--            ; wit     = wit⊥
--            ; relLock = V.replicate 0
--            ; outputs = (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ []
--            ; absLock = 0 }
--         λᶜ = submit T

--         -- (v) extend txout′ with {y↦T₀, y′↦T₁} (removing x↦T₀), sechash = sechash′, κ = κ′
--         open H₁₃ {R = Rˢ} 𝕣 t α t′ A v v′ x Γ₀ y y′ cfg≡ (T at 0F) (T at 1F) Γ→Γ′
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: authorize donate (similar to [10])
--   [14] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--        ∀ {x : Id} → let Γ = ⟨ A has v ⟩at x ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = auth-donate⦅ A , x ▷ᵈ B′ ⦆
--         Γ′  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-AuthDonate] refl

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) (here refl)
--       in
--       (∃λ : Any (λ l → ∃ λ B → ∃ λ T
--                 → (l ≡ B →∗∶ [ T ♯ ])
--                 × (inputs  T ≡ V.[ hashTxⁱ (txout′ {x} x∈) ])
--                 × (outputs T ≡ V.[ v -redeemableWith- K̂ B′ ])
--                 ) Rᶜ)
--     → let
--         T : ∃Tx
--         T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

--         -- (iii) broadcast transaction T, signed by A
--         m′ = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m′

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₄ {R = Rˢ} 𝕣 t α t′ A v x Γ₀ B′ cfg≡ Γ→Γ′
--       in
--       -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: donate (similar to [11])
--   [15] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
--        ∀ {x : Id} → let Γ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀; Γₜ = Γ at t in

--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = donate⦅ x ▷ᵈ B′ ⦆
--         Γ′  = ⟨ B′ has v ⟩at y ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-Donate] refl

--         x∈ : x ∈ namesʳ Rˢ
--         x∈ = subst (λ ◆ → x ∈ namesʳ ◆) (sym cfg≡) (here refl)

--         -- (iii) submit transaction T
--         T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
--            { inputs  = V.[ hashTxⁱ (txout′ {x} x∈) ]
--            ; wit     = wit⊥
--            ; relLock = V.replicate 0
--            ; outputs = V.[ v -redeemableWith- K̂ B′ ]
--            ; absLock = 0 }
--         λᶜ = submit T

--         -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
--         open H₁₅ {R = Rˢ} 𝕣 t α t′ A v x B′ Γ₀ y cfg≡ (T at 0F) Γ→Γ′
--       in
--       --——————————————————————————————————————————————————————————————————————
--       coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** After
--   [18] :
--     (δ>0 : δ > 0) →
--     let
--       Γₜ@(Γ at t) = lastCfgᵗ Rˢ
--       α   = delay⦅ δ ⦆
--       t′  = (t + δ)
--       Γₜ′ = Γ at t′
--       λᶜ  = delay δ

--       Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--       Γ→Γ′ = [Delay] δ>0

--       open H₁₈ {R = Rˢ} 𝕣 t α t′ Γ refl Γ→Γ′
--     in
--     --——————————————————————————————————————————————————————————————————————
--     coher₁₁ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′


-- data coher₁₂ where

--   -- ** Deposits: authorize destroy
--   [16] : ∀ {ds : List (Participant × S.Value × Id)} {j : Index ds} {xs : Ids}

--     → let
--         k  = length ds
--         xs = map (proj₂ ∘ proj₂) ds
--         A  = proj₁ (ds ‼ j)
--         j′ = ‼-map {xs = ds} j
--         Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
--         Γ  = Δ ∣ Γ₀
--         Γₜ = Γ at t
--       in
--       -- (ii) in Rˢ we find ⟨Bᵢ,vᵢ⟩yᵢ for i ∈ 1..k
--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = auth-destroy⦅ A , xs , j′ ⦆
--         Γ′  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-AuthDestroy] refl

--         -- (vii) txout = txout′, sechash = sechash′, κ = κ′
--         open H₁₆ {R = Rˢ} 𝕣 t α t′ ds Γ₀  j A y cfg≡ Γ→Γ′
--       in
--       -- (iii) in Rᶜ we find B → ∗ ∶ T, for some T having txout′(yᵢ) as inputs (+ possibly others)
--       (T : Tx i 0)
--     → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)
--     → (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ T ♯ ]) Rᶜ)

--     → let
--         -- (iv) broadcast transaction T, signed by A
--         m = [ SIG (K̂ A) T ]
--         λᶜ = B →∗∶ m
--       in
--       -- (v) λᶜ is the first broadcast of m in Rᶜ after the first broadcast of T
--       All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m) (Any-tail T∈)

--       -- (vi) λᶜ does not correspond to any *other* symbolic move
--     → (∀ α′ Γₜ′ (𝕣 : ℝ Rˢ) (𝕣′ : ℝ $ Γₜ′ ∷⟦ α′ ⟧ Rˢ)
--          → α′ ≢ α
--          → ¬ coher₁₁ Rˢ α′ Γₜ′ Rᶜ λᶜ 𝕣 𝕣′)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₂ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

--   -- ** Deposits: destroy
--   [17] : ∀ {ds : List (Participant × S.Value × Id)} {j : Index ds} {xs : Ids}

--     → let
--         xs = map (proj₂ ∘ proj₂) ds
--         Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds)
--         Γ  = Δ ∣ Γ₀
--         Γₜ = Γ at t
--       in
--       -- (ii) in Rˢ, α assumes ⟨Aᵢ,vᵢ⟩xᵢ to obtain 0
--       (cfg≡ : Rˢ ≡⋯ Γₜ)

--     → let
--         α   = destroy⦅ xs ⦆
--         Γ′  = Γ₀
--         t′  = t
--         Γₜ′ = Γ′ at t′

--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] [DEP-Destroy] refl

--         -- (v) txout = txout′, sechash = sechash′, κ = κ′
--         -- remove {⋯ xᵢ ↦ (Tᵢ,j) ⋯} from txout′
--         open H₁₇ {R = Rˢ} 𝕣 t α t′ ds Γ₀ y cfg≡ Γ→Γ′
--       in
--       (T : Tx i 0)
--     → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)

--     → let
--         -- (iii) submit transaction T
--         λᶜ = submit (_ , _ , T)
--       in

--       -- (iv) λᶜ does not correspond to any *other* symbolic move
--       (∀ α′ Γₜ′ (𝕣 : ℝ Rˢ) (𝕣′ : ℝ $ Γₜ′ ∷⟦ α′ ⟧ Rˢ)
--          → α′ ≢ α
--          → ¬ coher₁₁ Rˢ α′ Γₜ′ Rᶜ λᶜ 𝕣 𝕣′)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₁₂ Rˢ α Γₜ′ Rᶜ λᶜ 𝕣 𝕣′

-- data coher₂ Rˢ txout where

--   [1] :

--       Disjoint (V.toList $ inputs $ proj₂ $ proj₂ T) (hashTxⁱ <$> codom txout)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₂ Rˢ txout (submit T)

--   [2] :

--       (λᶜ ≡ A →O∶ m)
--     ⊎ (λᶜ ≡ O→ A ∶ m)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₂ Rˢ txout λᶜ

--   [3] : let λᶜ = A →∗∶ m in

--       -- λᶜ does not correspond to any symbolic move
--       (∀ α Γₜ Rᶜ (𝕣 : ℝ Rˢ) (𝕣′ : ℝ $ Γₜ ∷⟦ α ⟧ Rˢ)
--          → ¬ coher₁ Rˢ α Γₜ Rᶜ λᶜ 𝕣 𝕣′)
--       --——————————————————————————————————————————————————————————————————————
--     → coher₂ Rˢ txout λᶜ

-- T0D0: enforce common naming scheme via a module that re-exports names in a systematic way
-- e.g. [1]: open —→⟨ (advertise[ ⟨G⟩C ]) ≈ (A →∗∶ C) ⟩ (` ⟨G⟩C ∣ Γ) AT t
{-
module —→⟨_≈_⟩_AT_
  (`α : S.Label) (`λᶜ : C.Label)
  (`Γ′ : Cfg) (`t′ : S.Time)
  where
    private
      α   = `α
      Γ′  = `Γ′
      t′  = `t′
      Γₜ′ = `Γ′ at `t′
      λᶜ  = `λᶜ
-}
