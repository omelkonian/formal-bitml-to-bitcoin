{-# OPTIONS --no-forcing #-}
open import Prelude.Init hiding (T); open SetAsType
open L.Mem
open import Prelude.Lists.Core
open import Prelude.Lists.Indexed
open import Prelude.Lists.Collections
open import Prelude.Lists.Mappings
open import Prelude.Lists.Membership
open import Prelude.Lists.MapMaybe
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Traces
open import Prelude.Null
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Membership.Patterns

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Coherence (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
  hiding (_∎; begin_; d; Γₜ″; G; C)
  renaming (_∶_♯_ to _∶_#_; ⟨_∶_♯_⟩ to ⟨_∶_#_⟩)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Σ; t; t′; `; ∣_∣; n)
open import Compiler ⋯′ η
open import SecureCompilation.ComputationalContracts ⋯′
open import SecureCompilation.Helpers ⋯

private variable
  ⟨G⟩C ⟨G⟩C′ ⟨G⟩C″ : Ad
  𝕣  : ℝ Rˢ

_redeemable-by_ : S.Value → KeyPair → ∃TxOutput
v redeemable-by k = 1 , v locked-by ƛ versig [ k ] [ # 0 ]

-- * Inductive case 1
data _~₁₁_ : ℝ∗ Rˢ → CRun → Type where

  -- ** Stipulation: advertisting a contract
  [1] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {⟨G⟩C : Ad} (let open ∣AD ⟨G⟩C)
      (let Γₜ = Γ at t)
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = advertise⦅ ⟨G⟩C ⦆
        Γ′  = ` ⟨G⟩C ∣ Γ
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [C-Advertise]
      (vad : ValidAd ⟨G⟩C)
      (hon : Any (_∈ Hon) partG)
      (d⊆  : ⟨G⟩C ⊆⦅ deposits ⦆ Γ)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

        -- txout′ = txout, sechash′ = sechash, κ′ = κ
        open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈ using (λˢ)

        C =
          let
            txoutΓ = Txout Γ ∋ Txout≈ {Rˢ ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)
            txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
            txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
          in
            encodeAd ⟨G⟩C (txoutG , txoutC)
        λᶜ = A →∗∶ C
      in
      ────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Stipulation: committing secrets
  [2] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {⟨G⟩C} (open ∣AD ⟨G⟩C)
      {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C}
    → let
        Γ = ` ⟨G⟩C ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        C = encodeAd ⟨G⟩C (ad∈⇒Txout {⟨G⟩C}{Γ}{Rˢ} 𝟘 R≈ txout′)

        Δ : List (Secret × Maybe ℕ)
        Δ = map drop₃ Δ×h̅

        (as , ms) = unzip Δ

        Δᶜ = Cfg ∋ || map (uncurry ⟨ A ∶_#_⟩) Δ

        h̅ : List ℤ -- ≈ Message
        h̅ = map select₃ Δ×h̅

        k̅ : List ℤ -- ≈ Message
        k̅ = concatMap (map pub ∘ codom) (codom k⃗)

        C,h̅,k̅ = encode (C , h̅ , k̅)
        C,h̅,k̅ₐ = SIG (K A) C,h̅,k̅

        α   = auth-commit⦅ A , ⟨G⟩C , Δ ⦆
        Γ′  = Γ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
        t′  = t
        Γₜ′ = Γ′ at t′
        λᶜ  = B →∗∶ C,h̅,k̅ₐ
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) → let Γₜ″ = ∃Γ≈ .proj₁ at t′ in
      -- Hypotheses from [C-AuthCommit]
      (as≡ : as ≡ secretsOfᵖ A G)
      (All∉ : All (_∉ secretsOfᶜᶠ A Γ₀) as)
      (Hon⇒ : A ∈ Hon → All Is-just ms)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthCommit] as≡ All∉ Hon⇒) refl

        -- (v) txout = txout′ (vi) extend sechash′ (vii) extend κ′
        sechash⁺ : as ↦ ℤ
        sechash⁺ a∈ =
          let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
              (_ , _ , z) , _ = ∈-map⁻ drop₃ a×m∈
          in z

        open H₂ {Rˢ} 𝕣 t α t′ Γ R≈ A A ⟨G⟩C Δ sechash⁺ k⃗ Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      -- (i) ⟨G⟩C has been previously advertised in Rᶜ
    ∀ (∃λ : ∃ λ B → (B →∗∶ C) ∈ toList Rᶜ) →
      -- ∘ it is the first occurrence of such a broadcast in Rᶜ
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ C) (Any-tail $ ∃λ .proj₂)

      -- (ii) broadcast message in Rᶜ

      -- ∘ hashes respect security parameter η
    ∙ All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅

      -- ∘ make sure that λᶜ is the first occurrence of such a message after C in Rᶜ
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃λ .proj₂)

      -- (iii) each hᵢ is obtained by querying the oracle,
      --       otherwise we have a dishonestly chosen secret
    ∙ CheckOracleInteractions Rᶜ Δ×h̅

      -- (iv) no hash is reused
    ∙ Unique h̅
    ∙ Disjoint h̅ (codom sechash′)
      ────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Stipulation: authorizing deposits
  [3] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {⟨G⟩C} (let open ∣AD ⟨G⟩C)
    → let
        Γ = ` ⟨G⟩C ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-init⦅ A , ⟨G⟩C , x ⦆
        Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [C-AuthInit]
      (committedA : partG ⊆ committedParticipants ⟨G⟩C Γ₀)
      (A∈per : (A , v , x) ∈ persistentDeposits G)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        open H₃ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x R≈ Γ→Γ′ ∃Γ≈ committedA using (λˢ; T)

        -- (i) broadcast Tᵢₙᵢₜ , signed with A's private key
        m = SIG (K̂ A) T
        λᶜ = B →∗∶ m
      in
      -- (ii) Tᵢₙᵢₜ occurs as a message in Rᶜ
    ∀ (∃λ : ∃ λ B → (B →∗∶ (T ♯)) ∈ toList Rᶜ) →

      -- (iii) broadcast message in Rᶜ
      -- ∘ λᶜ is the first occurrence of such a message after Tinit in Rᶜ
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃λ .proj₂)
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Stipulation: activating the contract
  [4] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {⟨G⟩C} (let open ∣AD ⟨G⟩C)
    → let
        toSpend = persistentDeposits G
        vs      = map select₂ toSpend
        xs      = map select₃ toSpend
        v       = sum vs

        Γ = ` ⟨G⟩C ∣ Γ₀
          ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ⟨G⟩C ] })
                   toSpend
          ∣ || map (_auth[ ♯▷ ⟨G⟩C ]) partG
        Γₜ = Γ at t
      in
      -- (i) consume {G}C and its persistent deposits from Rˢ
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = init⦅ G , C ⦆
        Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [C-Init]
      (fresh-z : z ∉ xs ++ ids Γ₀) →
      let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-Init] fresh-z) refl

        -- (iii) sechash = sechash′, κ = κ′, txout extends txout′ with (z ↦ Tᵢₙᵢₜ)
        open H₄ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ toSpend v z R≈ Γ→Γ′ ∃Γ≈ using (λˢ; T)

        -- (ii) append Tᵢₙᵢₜ to the blockchain
        λᶜ = submit T
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Contract actions: authorize control
  [5] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {i : Index c} (let open ∣SELECT c i)
    → let
        Γ = ⟨ c , v ⟩at x ∣ Γ₀
        Γₜ = Γ at t
      in
      -- D ≡ A ∶ D′
      (D≡A:D′ : A ∈ authDecorations d)
      -- (i) Rˢ contains ⟨C , v⟩ₓ with C = D + ∑ᵢ Dᵢ
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-control⦅ A , x ▷ d ⦆
        Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [C-AuthControl], already in hypothesis `D≡A:D′`
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

        open H₅ {Rˢ} 𝕣 t α t′ c v x Γ₀ A i R≈ Γ→Γ′ ∃Γ≈ D≡A:D′ using (λˢ; T; pubK)

        λᶜ = B →∗∶ SIGᵖ pubK T
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Contract actions: put
  [6] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {ds : DepositRefs} (let (_ , vs , xs) = unzip₃ ds)
      {ss : List (Participant × Secret × ℕ)} (let (_ , as , _)  = unzip₃ ss)
      {i : Index c} (let open ∣SELECT c i; As , ts = decorations d)
    → let
        -- (i) xs = x₁⋯xₖ
        Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
        Δ   = || map (uncurry₃ _∶_#_) ss
        Γ₂  = Δ ∣ Γ₀
        Γ₁₂ = Γ₁ ∣ Γ₂
        Γ   = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₂)
        Γₜ  = Γ at t
      in
      -- ii) in Rˢ, α consumes ⟨D+C,v⟩y and the deposits ⟨Aᵢ,vᵢ⟩ₓᵢ to produce ⟨C′,v′⟩y′
      --     where D = ⋯ : put⋯reveal⋯.C′
      --     let t be the maximum deadline in an `after` in front of D
      --     T0D0: what should t′ be in case there are no `after` decorations? (currently any value)
      (t≡ : t ≡ maximum t ts)
      (d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′)
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = put⦅ xs , as , y ⦆
        Γ′  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [C-PutRev]
      (fresh-y′ : y′ ∉ y L.∷ ids Γ₁₂)
      (p⟦Δ⟧≡ : ⟦ p ⟧ᵖ Δ ≡ just true)
      -- Hypotheses from [Timeout]
      (As≡∅ : Null As)
    → let
        ∀≤t : All (_≤ t′) ts
        ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

        put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
        put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡
               ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Timeout] As≡∅ ∀≤t put→ refl

        open H₆ {Rˢ} 𝕣 t α t′ c v y ds ss Γ₂ c′ y′ i p R≈ Γ→Γ′ ∃Γ≈ d≡ using (λˢ; T)

        λᶜ = submit T
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Contract actions: authorize reveal
  [7] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)}
      (let Δ = map drop₃   Δ×h̅
           h̅ = map select₃ Δ×h̅)
      {⟨G⟩C} (let open ∣AD ⟨G⟩C) {k⃗ : 𝕂²′ ⟨G⟩C}
    → let
        Γ = ⟨ A ∶ a # just n ⟩ ∣ Γ₀
        Γₜ = Γ at t
      in
      ∣ m ∣ᵐ ≤ η
    → (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-rev⦅ A , a ⦆
        Γ′  = A ∶ a # n ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [C-AuthRev] refl

        a∈ : a ∈ secrets Rˢ
        a∈ = namesˡ⦅end⦆⊆ Rˢ
           $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ R≈ .proj₂) 𝟘
      in
      -- (ii) in Rᶜ we find ⋯ (B → O ∶ m) (O → B : sechash′(a)) for some B ⋯
      (∃ λ B → (B , m , sechash′ {a} a∈) ∈ oracleInteractionsᶜ Rᶜ)

      -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
    → (∃α : auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labelsʳ Rˢ)
    → a ∈ secrets G
    → let
        -- (iii) txout = txout′, sechash = sechash′, κ = κ′
        open H₇ 𝕣 t α t′ A a n Γ₀ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)

        -- (i) some participant B broadcasts message m
        open H₇′ 𝕣 t α t′ Δ h̅ k⃗ ∃α using (C,h̅,k̅)
        λᶜ = B →∗∶ m
      in
      -- ... with a corresponding broadcast of m′=(C,h̅,k̅) in Rᶜ
    ∀ (∃λ : ∃ λ B → B →∗∶ C,h̅,k̅ ∈ toList Rᶜ) →

      -- (v) λᶜ is the first broadcast of m after the first broadcast of m′
    ∙ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃λ .proj₂)
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Contract actions: split
  [8] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {i : Index c} (let open ∣SELECT c i; As , ts = decorations d)
      {vcis : VIContracts} (let vs , cs , xs = unzip₃ vcis; v = sum vs)
    → let
        Γ = ⟨ c , v ⟩at y ∣ Γ₀
        Γₜ = Γ at t
      in
      -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨C₀,v₀⟩ₓ₀ | ⋯ | ⟨Cₖ,vₖ⟩ₓₖ
      --     where D = ⋯ : split vs → cs
      --     let t be the maximum deadline in an `after` in front of D
      --     T0D0: what should t′ be in case there are not after decorations? (currently any value)
      (t≡ : t ≡ maximum t ts)
      (d≡ : d ≡⋯∶ split (zip vs cs))
      (R≈ : Rˢ ≈⋯ Γₜ)
      -- Hypotheses from [C-Split]
      (fresh-xs : All (_∉ y L.∷ ids Γ₀) xs)
      -- Hypotheses from [Timeout]
      (As≡∅ : Null As)
    → let
        α   = split⦅ y ⦆
        Γ′  = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        ∀≤t : All (_≤ t′) ts
        ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

        split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
        split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
              ~: [C-Split] {vcis = vcis} fresh-xs

        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Timeout] As≡∅ ∀≤t split→ refl

        open H₈ {Rˢ} 𝕣 t α t′ c v y Γ₀ i vcis R≈ Γ→Γ′ ∃Γ≈ d≡ using (λˢ; T)

        λᶜ = submit T
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Contract actions: withdraw
  [9] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {i : Index c} (let open ∣SELECT c i; As , ts = decorations d)
    → let
        Γ = ⟨ c , v ⟩at y ∣ Γ₀
        Γₜ = Γ at t
      in
      -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨A,v⟩ₓ (where D = ⋯ : withdraw A)
      (d≡ : d ≡⋯∶ withdraw A)
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = withdraw⦅ A , v , y ⦆
        Γ′  = ⟨ A has v ⟩at x ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [C-Withdraw]
      (fresh-x : x ∉ y L.∷ ids Γ₀)
      -- Hypotheses from [Timeout]
      (As≡∅ : Null As)
      (∀≤t : All (_≤ t) ts)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Timeout] As≡∅ ∀≤t
          (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x)
          refl

        open H₉ {Rˢ} 𝕣 t α t′ c v y Γ₀ A x i R≈ Γ→Γ′ ∃Γ≈ d≡ using (λˢ; T)

        λᶜ = submit T
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: authorize join
  [10] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    → let
        Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-join⦅ A , x ↔ x′ ⦆
        Γ′  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-AuthJoin] refl

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
      in
      (∃λ : ∃ λ B → ∃ λ T → flip Any (toList Rᶜ) $ λ l →
          (l ≡ B →∗∶ (T ♯))
        × (inputs  T ≡ (hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]))
        × (outputs T ≡ [ (v + v′) redeemable-by K̂ A ]))
    → let
        T : ∃Tx
        T = 2 , 1 , ∃λ .proj₂ .proj₁

        -- (iii) broadcast transaction T, signed by A
        m′ = SIG (K̂ A) T
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₀ {Rˢ} 𝕣 t α t′ A v x v′ x′ Γ₀ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front $ ∃λ .proj₂ .proj₂)
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: join
  [11] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    → let
        Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′
          ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = join⦅ x ↔ x′ ⦆
        Γ′  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [DEP-Join]
      (fresh-y : y ∉ x L.∷ x′ ∷ ids Γ₀)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-Join] fresh-y) refl

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
        -- (ii) submit transaction T
        T : ∃Tx
        T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = hashTxⁱ <$> [ txout′ {x} (n⊆ 𝟘) ⨾ txout′ {x′} (n⊆ 𝟙) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ (v + v′) redeemable-by K̂ A ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (iii) extend txout′ with y↦T₀ (removing {x↦_;x′↦_}), sechash = sechash′, κ = κ′
        open H₁₁ {Rˢ} 𝕣 t α t′ A v x v′ x′ y Γ₀ R≈ (T at 0F) Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: authorize divide (similar to [10])
  [12] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    → let
        Γ = ⟨ A has (v + v′) ⟩at x ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-divide⦅ A , x ▷ v , v′ ⦆
        Γ′  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-AuthDivide] refl

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ
            ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
      in
      (∃λ : ∃ λ B → ∃ λ T → flip Any (toList Rᶜ) $ λ l →
          (l ≡ B →∗∶ (T ♯))
        × (inputs  T ≡ [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ])
        × (outputs T ≡ [ v redeemable-by K̂ A ⨾ v′ redeemable-by K̂ A ]))
    → let
        T : ∃Tx
        T = 1 , 2 , ∃λ .proj₂ .proj₁

        -- (iii) broadcast transaction T, signed by A
        m′ = SIG (K̂ A) T
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₂ {Rˢ} 𝕣 t α t′ A v v′ x Γ₀ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front $ ∃λ .proj₂ .proj₂)
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: divide (similar to [11])
  [13] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    → let
        Γ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = divide⦅ x ▷ v , v′ ⦆
        Γ′  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [DEP-Divide]
      (fresh-ys : All (_∉ x L.∷ ids Γ₀ ) [ y ⨾ y′ ])
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-Divide] fresh-ys) refl

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆ = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

        -- (iii) submit transaction T
        T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ v redeemable-by K̂ A ⨾ v′ redeemable-by K̂ A ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (v) extend txout′ with {y↦T₀, y′↦T₁} (removing x↦T₀), sechash = sechash′, κ = κ′
        open H₁₃ {Rˢ} 𝕣 t α t′ A v v′ x Γ₀ y y′ R≈ (T at 0F) (T at 1F) Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: authorize donate (similar to [10])
  [14] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    → let
        Γ = ⟨ A has v ⟩at x ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-donate⦅ A , x ▷ᵈ B′ ⦆
        Γ′  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-AuthDonate] refl

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)
      in
      (∃λ : ∃ λ B → ∃ λ T → flip Any (toList Rᶜ) $ λ l →
          (l ≡ B →∗∶ (T ♯))
        × (inputs  T ≡ [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ])
        × (outputs T ≡ [ v redeemable-by K̂ B′ ]))
    → let
        T : ∃Tx
        T = 1 , 1 , ∃λ .proj₂ .proj₁

        -- (iii) broadcast transaction T, signed by A
        m′ = SIG (K̂ A) T
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₄ {Rˢ} 𝕣 t α t′ A v x Γ₀ B′ R≈ Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m′) (Any-front $ ∃λ .proj₂ .proj₂)
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: donate (similar to [11])
  [15] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
    → let
        Γ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = donate⦅ x ▷ᵈ B′ ⦆
        Γ′  = ⟨ B′ has v ⟩at y ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [DEP-Donate]
      (fresh-y : y ∉ x L.∷ ids Γ₀)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-Donate] fresh-y) refl

        n⊆ : Γ ⊆⦅ ids ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂)

        -- (iii) submit transaction T
        T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = [ hashTxⁱ (txout′ {x} $ n⊆ 𝟘) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = [ v redeemable-by K̂ B′ ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
        open H₁₅ {Rˢ} 𝕣 t α t′ A v x B′ Γ₀ y R≈ (T at 0F) Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)

  -- ** After
  [18] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      (δ>0 : δ > 0)
    → let
        Γₜ@(Γ at t) = Rˢ .end
        α   = delay⦅ δ ⦆
        t′  = t + δ
        Γₜ′ = Γ at t′
        λᶜ  = delay δ
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Delay] δ>0

        open H₁₈ {Rˢ} 𝕣 t α t′ Γ (≈ᵗ-refl {Γₜ}) Γ→Γ′ ∃Γ≈ using (λˢ)
      in
      ─────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)


_≁₁₁_ : ℝ∗ Rˢ → CRun → Type
_≁₁₁_ = ¬_ ∘₂ _~₁₁_

data _~₁₂_ : ℝ∗ Rˢ → CRun → Type where

  -- ** Deposits: authorize destroy
  [16] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {ds : DepositRefs} (let k = length ds; xs = map (proj₂ ∘ proj₂) ds)
      {j : Index ds} (let A = (ds ‼ j) .proj₁; j′ = ‼-map {xs = ds} j)
    → let
        Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
        Γ  = Δ ∣ Γ₀
        Γₜ = Γ at t
      in
      -- (ii) in Rˢ we find ⟨Bᵢ,vᵢ⟩yᵢ for i ∈ 1..k
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-destroy⦅ A , xs , j′ ⦆
        Γ′  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
      -- Hypotheses from [DEP-AuthDestroy]
      (fresh-y : y ∉ ids Γ₀)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-AuthDestroy] fresh-y) refl

        -- (vii) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₆ {Rˢ} 𝕣 t α t′ ds Γ₀  j A y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
      in
      -- (iii) in Rᶜ we find B → ∗ ∶ T
      --       for some T having txout′(yᵢ) as inputs (+ possibly others)
      (T : Tx i 0)
    → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)
    → (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ (T ♯)) (toList Rᶜ))
    → let
        -- (iv) broadcast transaction T, signed by A
        m = SIG (K̂ A) T
        λᶜ = B →∗∶ m
      in
      -- (v) λᶜ is the first broadcast of m in Rᶜ after the first broadcast of T
    ∙ All (λ l → ∀ B → l ≢ B →∗∶ m) (Any-front T∈)
      -- (vi) λᶜ does not correspond to any *other* symbolic move
    ∙ (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
        → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
        → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))
      ──────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓)

  -- ** Deposits: destroy
  [17] :
    ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣)
      {ds : DepositRefs} (let xs = map (proj₂ ∘ proj₂) ds)
      {j : Index ds}
    → let
        Δ  = || flip map (enumerate ds) (λ{ (i , Aᵢ , vᵢ , xᵢ) →
                  ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
        Γ  = Δ ∣ Γ₀
        Γₜ = Γ at t
      in
      -- (ii) in Rˢ, α assumes ⟨Aᵢ,vᵢ⟩xᵢ to obtain 0
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = destroy⦅ xs ⦆
        Γ′  = Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′)) (let Γₜ″ = ∃Γ≈ .proj₁ at t′)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-Destroy] refl

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        -- remove {⋯ xᵢ ↦ (Tᵢ,j) ⋯} from txout′
        open H₁₇ {Rˢ} 𝕣 t α t′ ds Γ₀ y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
      in
      (T : Tx i 0)
    → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)
    → let
        -- (iii) submit transaction T
        λᶜ = submit (_ , _ , T)
      in
      -- (iv) λᶜ does not correspond to any *other* symbolic move
      (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
        → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
        → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))
      ─────────────────────────────────────────────────────────────
      (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓)

_≁₁₂_ : ℝ∗ Rˢ → CRun → Type
_≁₁₂_ = ¬_ ∘₂ _~₁₂_

data _~₁_ : ℝ∗ Rˢ → CRun → Type where

  [L]_ : ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
    ──────────────────────────────
    (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁  (λᶜ ∷ Rᶜ ✓)

  [R]_ : ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓)
    ──────────────────────────────
    (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁  (λᶜ ∷ Rᶜ ✓)

_≁₁_ : ℝ∗ Rˢ → CRun → Type
_≁₁_ = ¬_ ∘₂ _~₁_

-- * Inductive case 2
data _~₂_∷ʳ_ (𝕣∗ : ℝ∗ Rˢ) (Rᶜ : CRun) : C.Label → Type where

  [1] : ∀ {T} (let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣) →
    T .proj₂ .proj₂ .inputs ♯ (hashTxⁱ <$> codom txout′)
    ────────────────────────────────────────────────────
    𝕣∗ ~₂ Rᶜ ∷ʳ submit T

  [2] :
    (λᶜ ≡ A →O∶ m) ⊎ (λᶜ ≡ O→ A ∶ m)
    ────────────────────────────────
    𝕣∗ ~₂ Rᶜ ∷ʳ λᶜ

  [3] :
    let λᶜ = A →∗∶ m in
    -- λᶜ does not correspond to any symbolic move
    (∀ {Γₜ} (λˢ : 𝕃 Rˢ Γₜ) → (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ≁₁ (λᶜ ∷ Rᶜ ✓))
    ──────────────────────────────────────────────────────────
    𝕣∗ ~₂ Rᶜ ∷ʳ λᶜ

data _~′_ : ℝ∗ Rˢ → CRun → Type where

  -- * Base case
  base :
    ∀ {ℽ : ℾᵗ Γₜ₀} (let open ℾᵗ ℽ; Γ₀ = Γₜ₀ .cfg)
      -- (i) Rˢ = Γ₀ ∣ 0, with Γ₀ initial
      (init : Initial Γₜ₀)
      -- (ii) Rᶜ = T₀ ⋯ initial
      (cinit : Initial Rᶜ) →
     -- (iii) generation of public keys, we do not consider that here
      -- (iv) ⟨A,v⟩ₓ ∈ Γ₀ ⇒ txout{ x ↦ (v$ spendable with K̂(A)(rₐ)) ∈ T₀ }
    ∙ (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
        let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
        ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
               × (T₀ ‼ᵒ oᵢ ≡ v redeemable-by K̂ A))
      -- (v)  dom sechash = ∅
      -- (vi) dom κ       = ∅
      -- by definition of Initial/ℝ
      ──────────────────────────────────────────────────────────────────────
      (ℽ ∎⊣ init ✓) ~′ Rᶜ

  -- * Inductive case 1
  step₁ : ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} {λˢ : 𝕃 Rˢ Γₜ} →
    ∙ 𝕣∗ ~′ Rᶜ
    ∙ (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁ (λᶜ ∷ Rᶜ ✓)
      ─────────────────────────────
      (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ~′ (λᶜ ∷ Rᶜ ✓)

  -- * Inductive case 2
  step₂ : ∀ {Rˢ} {𝕣∗ : ℝ∗ Rˢ} →
    ∙ 𝕣∗ ~′ Rᶜ
    ∙ 𝕣∗ ~₂ Rᶜ ∷ʳ λᶜ
      ───────────────
      𝕣∗ ~′ (λᶜ ∷ Rᶜ ✓)

_~_ _≁_ : S.Run → CRun → Type
Rˢ ~ Rᶜ = ∃ λ (𝕣∗ : ℝ∗ Rˢ) → 𝕣∗ ~′ Rᶜ
_≁_ = ¬_ ∘₂ _~_

private
  testPatternMatch-~ : Rˢ ~ Rᶜ → ⊤
  testPatternMatch-~ (𝕣∗ , coh) with coh
  ... | base init cinit txout≈ = tt
  ... | step₂ _ ([1] ins♯) = tt
  ... | step₂ _ ([2] λᶜ≡) = tt
  ... | step₂ _ ([3] ¬p) = tt
  ... | step₁ _ p with p
  ... | [L] [1]  R≈ ∃Γ≈ vad hon d⊆ = tt
  ... | [L] [2]  R≈ ∃Γ≈ as≡ All∉ Hon⇒ ∃B first-∃B h≡ first-λᶜ h∈O unique-h h♯ = tt
  ... | [L] [3]  R≈ ∃Γ≈ committedA A∈per ∃B first-∃B = tt
  ... | [L] [4]  R≈ ∃Γ≈ fresh-z = tt
  ... | [L] [5]  d≡ R≈ ∃Γ≈ = tt
  ... | [L] [6]  t≡ d≡ R≈ ∃Γ≈ fresh-y′ p⟦Δ⟧≡ As≡∅ = tt
  ... | [L] [7]  m≤ R≈ ∃Γ≈ ∃B ∃α a∈ ∃λ first-λᶜ = tt
  ... | [L] [8]  t≡ d≡ R≈ fresh-xs As≡∅ ∃Γ≈ = tt
  ... | [L] [9]  d≡ R≈ ∃Γ≈ frsg-x As≡∅ ∀≤t = tt
  ... | [L] [10] R≈ ∃Γ≈ ∃λ first-λᶜ = tt
  ... | [L] [11] R≈ ∃Γ≈ fresh-y = tt
  ... | [L] [12] R≈ ∃Γ≈ ∃λ first-λᶜ = tt
  ... | [L] [13] R≈ ∃Γ≈ fresh-ys = tt
  ... | [L] [14] R≈ ∃Γ≈ ∃λ first-λᶜ = tt
  ... | [L] [15] R≈ ∃Γ≈ fresh-y = tt
  ... | [R] [16] R≈ ∃Γ≈ fresh-y T ⊆ins T∈ first-λᶜ ¬coh = tt
  ... | [R] [17] R≈ ∃Γ≈ T ⊆ins ¬coh = tt
  ... | [L] [18] δ>0 ∃Γ≈ = tt
