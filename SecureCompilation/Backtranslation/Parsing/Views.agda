-----------------------------------------------
-- Parsing computational runs to symbolic ones.
-----------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding (T); open SetAsType
open L.Mem using (_∈_; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership hiding (_∈_)
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.InferenceRules
open import Prelude.Lists.Collections
open import Prelude.Semigroup
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.General
open import Prelude.Tactics.Existentials
open import Prelude.Views

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Backtranslation.Parsing.Views (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
  hiding (Rˢ′; d; Σ)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Σ; t; t′; `; ∣_∣; n)

open import SecureCompilation.ComputationalContracts ⋯′
open import Compiler ⋯′ η
open import Coherence ⋯ as SC

-- [BUG] See issue #5464
_≈ᶜ_ = _≈_ ⦃ Setoid-Cfg ⦄

module _ (Rˢ : S.Run) (𝕣∗ : ℝ∗ Rˢ) (Rᶜ : CRun) where
  𝕣 = ℝ∗⇒ℝ 𝕣∗
  open ℝ 𝕣

  try-decode : ∀ m → Dec $
    ∃ λ ad → ∃ λ (txoutG : Txout ad) → ∃ λ (txoutC : Txout (ad .C)) →
      m ≡ encodeAd ad (txoutG , txoutC)
  try-decode m
    with decode′ {A = Advertisementᶜ} m
  ... | no m≢ = no λ (ad , txoutG , txoutC , m≡) →
    m≢ (reify (ad , txoutG , txoutC) , m≡)
  ... | yes (adᶜ , m≡)
    with idsᶜ adᶜ ⊆? codom txout′
  ... | no ids⊈ = no λ (ad , txoutG , txoutC , m≡) →
    ids⊈ {!!}
  ... | yes ids⊆ =
    let ad , txoutG , txoutC = abstractᶜ adᶜ (codom-↦ txout′ ∘ ids⊆)
        open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)
    in yes (ad , txoutG , txoutC ,
      (begin≡
        m
      ≡⟨ m≡ ⟩
        encode adᶜ
      ≡⟨ cong encode $ sym $ reify∘abstract adᶜ (codom-↦ txout′ ∘ ids⊆) ⟩
        encode (reify (ad , txoutG , txoutC))
      ≡⟨⟩
        encodeAd ad (txoutG , txoutC)
      ∎≡
      ))

  module _ (A₀ : Participant) (m₀ : Message) where

    open import Prelude.Irrelevance

    -- THESE DO NOT HOLD
    -- postulate
    --   instance
    --     Squashed-⊆ : ∀ {A : Type ℓ} {xs ys : List A} → Squashed (xs ⊆ ys)
    --     Squashed-∈ : ∀ {A : Type ℓ} {x : A} {xs : List A} → Squashed (x ∈ xs)
    --     Squashed-∉ : ∀ {A : Type} {x : A} {xs : List A} → Squashed (x ∉ xs)
        -- Squashed-↭ : ∀ {A : Type ℓ} {xs ys : List A} → Squashed (xs ↭ ys)

    module _ (⟨G⟩C : Ad) where
      ℍ[1]₀ : Type
      ℍ[1]₀ = let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G; Γ = Rˢ ∙cfg in
          Valid ⟨G⟩C
        × Any (_∈ Hon) partG
        × (⟨G⟩C ⊆⦅ deposits ⦆ Γ)

      ℍ[1]?₀ : Dec ℍ[1]₀
      ℍ[1]?₀ = let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G in
              Valid? ⟨G⟩C
        ×-dec any? (_∈? Hon) partG
        ×-dec (deposits ⟨G⟩C ⊆? deposits (Rˢ ∙cfg))

      ℍ[1] : Type
      ℍ[1] = let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G; Γ = Rˢ ∙cfg in
        ∃ λ (vad : Valid ⟨G⟩C)
        → Any (_∈ Hon) partG
        × ∃ λ (d⊆ : ⟨G⟩C ⊆⦅ deposits ⦆ Γ) →
        let
          txoutΓ = Txout Γ ∋ 𝕣 ∙txoutEnd_
          txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
          txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
          C = encodeAd ⟨G⟩C (txoutG , txoutC)
        in
         m₀ ≡ C

      EQ₀ : let ⟨ G ⟩ _ = ⟨G⟩C; Γ = Rˢ ∙cfg in
        ∀ (d⊆ d⊆′ : ⟨G⟩C ⊆⦅ deposits ⦆ Γ) →
        let
          txoutΓ  = Txout Γ ∋ 𝕣 ∙txoutEnd_
          txoutG  = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
          txoutG′ = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆′)
        in
          txoutG ≗↦ txoutG′
      EQ₀ d⊆ d⊆′ = {!!}

      EQ₁ : ∀ (txoutG : Txout ⟨G⟩C) (vad vad′ : Valid ⟨G⟩C) →
        let
          ⟨ _ ⟩ C = ⟨G⟩C
          txoutC  = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad  ∙names-⊆)
          txoutC′ = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad′ ∙names-⊆)
        in
          txoutC ≗↦ txoutC′
      EQ₁ txoutG vad vad′ = {!!}

      EQ : let ⟨ G ⟩ C = ⟨G⟩C ; Γ = Rˢ ∙cfg in
        ∀ (vad vad′ : Valid ⟨G⟩C) (d⊆ d⊆′ : ⟨G⟩C ⊆⦅ deposits ⦆ Γ) →
        let
          txoutΓ = Txout Γ ∋ 𝕣 ∙txoutEnd_

          txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
          txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)

          txoutG′ = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆′)
          txoutC′ = Txout C ∋ weaken-↦ txoutG′ (mapMaybe-⊆ isInj₂ $ vad′ ∙names-⊆)
        in (txoutG ≗↦ txoutG′)
         × (txoutC ≗↦ txoutC′)
      EQ vad vad′ d⊆ d⊆′ = {!!}

      ℍ[1]? : Dec ℍ[1]
      ℍ[1]? = let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G; Γ = Rˢ ∙cfg in
        case Valid? ⟨G⟩C of λ where
        (no ¬vad) → no λ (vad , _) → ¬vad vad
        (yes vad) →
          case any? (_∈? Hon) partG of λ where
          (no ¬hon) → no λ (_ , hon , _) → ¬hon hon
          (yes hon) →
            case deposits ⟨G⟩C ⊆? deposits Γ of λ where
            (no  d⊈)  → no λ (_ , _ , d⊆ , _) → d⊈ d⊆
            (yes d⊆)  →
              let
                txoutΓ = Txout Γ ∋ 𝕣 ∙txoutEnd_
                txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
                txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
                C = encodeAd ⟨G⟩C (txoutG , txoutC)
              in
              case m₀ ≟ C of λ where
              (yes m≡) → yes (vad , hon , {!!}) -- d⊆ , m≡)
              (no  m≢) → no λ (vad , hon , d⊆ , m≡) → {!m≢ m≡!}

      -- ℍ[1]? = let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G in
      --   {!(Valid? ⟨G⟩C) ∃-dec λ vad → ?!}
        -- (Valid? ⟨G⟩C) ∃-dec λ vad
        -- → any? (_∈? Hon) partG
        -- ×-dec (deposits ⟨G⟩C ⊆? deposits (Rˢ ∙cfg)) ∃-dec λ d⊆ →
        -- let
        --   Γ = Rˢ ∙cfg
        --   txoutΓ = Txout Γ ∋ 𝕣 ∙txoutEnd_
        --   txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
        --   txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)
        --   C = encodeAd ⟨G⟩C (txoutG , txoutC)
        -- in
        --  m₀ ≟ C

    ∃ℍ[1] = ∃ λ ⟨G⟩C → ℍ[1] ⟨G⟩C

    -- T0D0: bundle _~_ proofs immediately in the view
    data DecodeBroadcastResponse : Type where

      [1] : ∀ ⟨G⟩C →

        ℍ[1]₀ ⟨G⟩C
        ───────────────────────
        DecodeBroadcastResponse

    -- try-decode-[1] : Dec ∃ℍ[1]
    -- try-decode-[1]
    --   with try-decode {Rˢ = Rˢ} 𝕣∗ m₀
    -- ... | no m≢ = no λ (_ , _ , _ , _ , m≡) → m≢ (_ , m≡)
    -- ... | yes (⟨G⟩C , m≡)
    --   with ℍ[1]? ⟨G⟩C
    -- ... | yes h = yes (-, h)
    -- ... | no ¬[1] = no go
    --   where
    --     go : ¬ ∃ℍ[1]
    --     go (_ , h@(_ , _ , _ , m≡′))
    --       rewrite encode-injective 𝕣 {ad = ⟨G⟩C} (trans (sym m≡) m≡′)
    --       = ¬[1] h

    postulate
      decodeBroadcast : DecodeBroadcastResponse
    -- decodeBroadcast
    --   with decode′ m₀ as Advertisementᶜ
    -- ... | no m≢
    --   = ?
    -- ... | yes (adᶜ , m≡)
    --   = ?
    {-
      ad , txoutC , txoutG

    -}

      -- with try-decodeAd {Rˢ = Rˢ} 𝕣∗ m₀
      -- = {![1] !}


    --   with try-decodeAd {Rˢ = Rˢ} 𝕣∗ m₀
    -- ... | no m≢ = ?
    -- ... | yes (⟨G⟩C , txoutG , txoutC)
    --   with ℍ[1]?₀ ⟨G⟩C
    -- ... | no ¬[1]₀ = ?
    -- ... | yes (vad , hon , d⊆)
    --   with m₀ ≟ encode
    --   = ?
    --   with try-decode-[1]u
    -- ... | yes (⟨G⟩C , h) = [1] ⟨G⟩C h
    -- ... | no ¬[1]

{-
    module _ ⟨G⟩C Δ×h̅ (k⃗ : 𝕂²′ ⟨G⟩C) A Γ₀ t where
      ℍ[2] : Type
      ℍ[2] =
        let
          ⟨ G ⟩ C = ⟨G⟩C
          Γ = ` ⟨G⟩C ∣ Γ₀
          Γₜ = Γ at t

          txoutG , txoutC = ad∈⇒Txout {⟨G⟩C}{Γ}{Rˢ} (here refl) R≈ txout′
          C = encodeMsg $ reifyᵃᵈ $ view (⟨G⟩C , (λ {_} → txoutG) , (λ {_} → txoutC))

          Δ : List (Secret × Maybe ℕ)
          Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

          (as , ms) = unzip Δ

          h̅ : List ℤ -- ≈ Message
          h̅ = map (proj₂ ∘ proj₂) Δ×h̅

          k̅ : List ℤ -- ≈ Message
          k̅ = concatMap (map pub ∘ codom) (codom k⃗)

          C,h̅,k̅ : Message
          C,h̅,k̅ = encode (C , h̅ , k̅)

          C,h̅,k̅ₐ : Message
          C,h̅,k̅ₐ = SIG (K A) C,h̅,k̅
        in
          (Rˢ ≈⋯ Γₜ)
        × (as ≡ secretsOfᵖ A G)
        × All (_∉ secretsOfᶜᶠ A Γ₀) as
        × (A ∈ Hon → All Is-just ms)
        × (∃ λ B → (B →∗∶ C) ∈ toList Rᶜ)
        × All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅
        × CheckOracleInteractions Rᶜ Δ×h̅
        × Unique h̅
        × Disjoint h̅ (codom sechash′)
        × (m₀ ≡ C,h̅,k̅ₐ)

      ℍ[2]? : Dec ℍ[2]
      ℍ[2]? =
        let
          ⟨ G ⟩ C = ⟨G⟩C
          Γ = ` ⟨G⟩C ∣ Γ₀
          Γₜ = Γ at t

          txoutG , txoutC = ad∈⇒Txout {⟨G⟩C}{Γ}{Rˢ} (here refl) R≈ txout′
          C = encodeMsg $ reifyᵃᵈ $ view (⟨G⟩C , (λ {_} → txoutC) , (λ {_} → txoutG))

          Δ : List (Secret × Maybe ℕ)
          Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

          (as , ms) = unzip Δ

          h̅ : List ℤ -- ≈ Message
          h̅ = map (proj₂ ∘ proj₂) Δ×h̅

          k̅ : List ℤ -- ≈ Message
          k̅ = concatMap (map pub ∘ codom) (codom k⃗)

          C,h̅,k̅ : Message
          C,h̅,k̅ = encode (C , h̅ , k̅)

          C,h̅,k̅ₐ : Message
          C,h̅,k̅ₐ = SIG (K A) C,h̅,k̅
        in
              (Rˢ ≈⋯? Γₜ)
        ×-dec (as ≟ secretsOfᵖ A G)
        ×-dec all? (_∉? secretsOfᶜᶠ A Γ₀) as
        ×-dec Hon⇒?
        ×-dec ∃[ toList Rᶜ ∋? C ]
        ×-dec all? (λ hᵢ → ∣ hᵢ ∣ᶻ ≟ η) h̅
        ×-dec CheckOracleInteractions? Rᶜ Δ×h̅
        ×-dec unique? h̅
        ×-dec disjoint? h̅ (codom sechash′)
        ×-dec (m₀ ≟ C,h̅,k̅ₐ)
        where
          Hon⇒? : ∀ {ms} → Dec (A ∈ Hon → All Is-just ms)
          Hon⇒? {ms}
            with A ∈? Hon
          ... | no A∉  = yes λ A∈ → ⊥-elim $ A∉ A∈
          ... | yes A∈
            with all? (M.Any.dec λ _ → yes tt) ms
          ... | no ¬p = no λ p → ¬p (p A∈)
          ... | yes p = yes λ _ → p

          ∃B×mᵢ? : ∀ Nᵢ hᵢ os → Dec (∃ λ B → ∃ λ mᵢ → ((B , mᵢ , [ hᵢ ]) ∈ os) × (∣ mᵢ ∣ᵐ ≡ η + Nᵢ))
          ∃B×mᵢ? Nᵢ hᵢ [] = no λ where (_ , _ , () , _)
          ∃B×mᵢ? Nᵢ hᵢ ((B , mᵢ , hs) ∷ os)
            with (hs ≟ [ hᵢ ]) ×-dec (∣ mᵢ ∣ᵐ ≟ η + Nᵢ)
          ... | yes (refl , m≡) = yes (B , mᵢ , here refl , m≡)
          ... | no ¬eq
            with ∃B×mᵢ? Nᵢ hᵢ os
          ... | yes (B , mᵢ , B∈ , m≡) = yes (B , mᵢ , there B∈ , m≡)
          ... | no  ∄B×mᵢ = no λ where
            (B , mᵢ , here refl , m≡) → ¬eq (refl , m≡)
            (B , mᵢ , there B∈  , m≡) → ∄B×mᵢ (B , mᵢ , B∈ , m≡)

          CheckOracleInteractions? : Decidable² CheckOracleInteractions
          CheckOracleInteractions? Rᶜ Δ×h̅ = let os = oracleInteractionsᶜ Rᶜ in
            all? (λ where
              (_ , just Nᵢ , hᵢ) →
                ∃B×mᵢ? Nᵢ hᵢ os
              (_ , nothing , hᵢ) →
                [ hᵢ ] ∉? map (proj₂ ∘ proj₂) (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ proj₁ ∘ proj₂) os))
              Δ×h̅

    ∃ℍ[2] = ∃ λ ⟨G⟩C → ∃ λ Δ×h̅ → ∃ λ (k⃗ : 𝕂²′ ⟨G⟩C) → ∃ λ A → ∃ λ Γ₀ → ∃ λ t →
      ℍ[2] ⟨G⟩C Δ×h̅ k⃗ A Γ₀ t

    module _ (⟨G⟩C : Ad) Γ₀ t A v x where
      ℍ[3] : Type
      ℍ[3] =
          let ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG; Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = auth-init⦅ A , ⟨G⟩C , x ⦆
            Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          ∃ λ (committedA : partG ⊆ committedParticipants ⟨G⟩C Γ₀)
        → ∃ λ (A∈per : (A , v , x) ∈ persistentDeposits G)
        → let
            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

            open H₃ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x R≈ Γ→Γ′ ∃Γ≈ committedA using (T)
          in
          (∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ)
        × (m₀ ≡ [ SIG (K̂ A) T ])

      ℍ[3]? : Dec ℍ[3]
      ℍ[3]? =
          let ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG; Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in
          (Rˢ ≈⋯? Γₜ) ∃-dec λ R≈
        → let
            α   = auth-init⦅ A , ⟨G⟩C , x ⦆
            Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (partG ⊆? committedParticipants ⟨G⟩C Γ₀) ∃-dec λ committedA
        → ((A , v , x) ∈? persistentDeposits G) ∃-dec λ A∈per
        → let
            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

            open H₃ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x R≈ Γ→Γ′ ∃Γ≈ committedA using (T)
          in
                ∃[ toList Rᶜ ∋? [ T ♯ ] ]
          ×-dec (m₀ ≟ [ SIG (K̂ A) T ])

    ∃ℍ[3] = ∃ λ ⟨G⟩C → ∃ λ Γ₀ → ∃ λ t → ∃ λ A → ∃ λ v → ∃ λ x →
      ℍ[3] ⟨G⟩C Γ₀ t A v x
{-
    module _ A v x Γ₀ t c (i : Index c) where
      ℍ[5] : Type
      ℍ[5] =
        let open ∣SELECT c i; Γ = ⟨ c , v ⟩at x ∣ Γ₀; Γₜ = Γ at t in
        ∃ λ (D≡A:D′ : A ∈ authDecorations d) →
        ∃ λ (R≈ : Rˢ ≈⋯ Γₜ) →
        let
          α   = auth-control⦅ A , x ▷ d ⦆
          Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
          t′  = t
          Γₜ′ = Γ′ at t′

          ∃Γ≈ : ∃ (_≈ᶜ Γ′)
          ∃Γ≈ = Γ′ , ↭-refl

          Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
          Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

          open H₅ {Rˢ} 𝕣 t α t′ c v x Γ₀ A i R≈ Γ→Γ′ ∃Γ≈ D≡A:D′ using (T; Kᵈ)
        in
        m₀ ≡ [ SIG Kᵈ T ]

      ℍ[5]? : Dec ℍ[5]
      ℍ[5]? =
        let open ∣SELECT c i; Γ = ⟨ c , v ⟩at x ∣ Γ₀; Γₜ = Γ at t in
        (A ∈? authDecorations d) ∃-dec λ D≡A:D′ →
        (Rˢ ≈⋯? Γₜ) ∃-dec λ R≈ →
        let
          α   = auth-control⦅ A , x ▷ d ⦆
          Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
          t′  = t
          Γₜ′ = Γ′ at t′

          ∃Γ≈ : ∃ (_≈ᶜ Γ′)
          ∃Γ≈ = Γ′ , ↭-refl

          Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
          Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

          open H₅ {Rˢ} 𝕣 t α t′ c v x Γ₀ A i R≈ Γ→Γ′ ∃Γ≈ D≡A:D′ using (T; Kᵈ)
        in
        m₀ ≟ [ SIG Kᵈ T ]

    ∃ℍ[5] = ∃ λ A → ∃ λ v → ∃ λ x → ∃ λ Γ₀ → ∃ λ t → ∃ λ c → ∃ λ i →
      ℍ[5] A v x Γ₀ t c i

    module _ ⟨G⟩C A a n Γ₀ t (Δ×h̅ : List (Secret × Maybe ℕ × ℤ)) (k⃗ : 𝕂²′ ⟨G⟩C) where
      ℍ[7] : Type
      ℍ[7] =
          let Γ = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀; Γₜ = Γ at t; ⟨ G ⟩ C = ⟨G⟩C in
          (∣ m₀ ∣ᵐ ≤ η)
        × ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            C : Message
            C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

            Δ : List (Secret × Maybe ℕ)
            Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

            h̅ : Message
            h̅ = map (proj₂ ∘ proj₂) Δ×h̅

            k̅ : Message
            k̅ = concatMap (map pub ∘ codom) (codom k⃗)

            a∈ : a ∈ namesˡ Rˢ
            a∈ = namesˡ⦅end⦆⊆ Rˢ
                $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈) (here refl)

            C,h̅,k̅ : Message
            C,h̅,k̅ = C ◇ h̅ ◇ k̅
          in
          (∃ λ B → (B , m₀ , [ sechash′ {a} a∈ ]) ∈ oracleInteractionsᶜ Rᶜ)
        × auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labels Rˢ
        × a ∈ namesˡ G
        × ∃ λ (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) (toList Rᶜ))
        → All (λ l → ∀ X → l ≢ X →∗∶ m₀) (Any-tail ∃λ)

      ℍ[7]? : Dec ℍ[7]
      ℍ[7]? = {!!}

    ∃ℍ[7] = ∃ λ ⟨G⟩C → ∃ λ A → ∃ λ a → ∃ λ n → ∃ λ Γ₀ → ∃ λ t → ∃ λ Δ×h̅ → ∃ λ (k⃗ : 𝕂²′ ⟨G⟩C) →
      ℍ[7] ⟨G⟩C A a n Γ₀ t Δ×h̅ k⃗

    module _ A v x v′ x′ Γ₀ t where
      ℍ[10] : Type
      ℍ[10] =
          let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀; Γₜ = Γ at t in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = auth-join⦅ A , x ↔ x′ ⦆
            Γ′  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
            x∈′ = n⊆ (there $′ here refl)
          in
          ∃ λ (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                    → (l ≡ B →∗∶ [ T ♯ ])
                    × (inputs  T ≡ hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ [])
                    × (outputs T ≡ [ 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
                    ) (toList Rᶜ))
        → let
            T : ∃Tx
            T = 2 , 1 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

            m′ = [ SIG (K̂ A) T ]
            -- λᶜ = B →∗∶ m′
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
        × (m₀ ≡ m′)

      ℍ[10]? : Dec ℍ[10]
      ℍ[10]? = {!!}

    ∃ℍ[10] = ∃ λ A → ∃ λ v → ∃ λ x → ∃ λ v′ → ∃ λ x′ → ∃ λ Γ₀ → ∃ λ t →
      ℍ[10] A v x v′ x′ Γ₀ t

    module _ A v v′ x Γ₀ t where
      ℍ[12] : Type
      ℍ[12] =
          let Γ = ⟨ A has (v + v′) ⟩at x ∣ Γ₀; Γₜ = Γ at t in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
          in
          ∃ λ (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                    → (l ≡ B →∗∶ [ T ♯ ])
                    × (inputs  T ≡ [ hashTxⁱ (txout′ {x} x∈) ])
                    × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
                    ) (toList Rᶜ))
        → let
            T : ∃Tx
            T = 1 , 2 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

            m′ = [ SIG (K̂ A) T ]
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
        × (m₀ ≡ m′)

      ℍ[12]? : Dec ℍ[12]
      ℍ[12]? = {!!}

    ∃ℍ[12] = ∃ λ A → ∃ λ v → ∃ λ v′ → ∃ λ x → ∃ λ Γ₀ → ∃ λ t →
      ℍ[12] A v v′ x Γ₀ t

    module _ A v x Γ₀ t B′ where
      ℍ[14] : Type
      ℍ[14] =
          let Γ = ⟨ A has v ⟩at x ∣ Γ₀; Γₜ = Γ at t in
        ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
          in
        ∃ λ (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                    → (l ≡ B →∗∶ [ T ♯ ])
                    × (inputs  T ≡ [ hashTxⁱ (txout′ {x} x∈) ])
                    × (outputs T ≡ [ v -redeemableWith- K̂ B′ ])
                    ) (toList Rᶜ))
        → let
            T : ∃Tx
            T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

            m′ = [ SIG (K̂ A) T ]
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
        × (m₀ ≡ m′)

      ℍ[14]? : Dec ℍ[14]
      ℍ[14]? = {!!}

    ∃ℍ[14] = ∃ λ A → ∃ λ v → ∃ λ x → ∃ λ Γ₀ → ∃ λ t → ∃ λ B′ →
      ℍ[14] A v x Γ₀ t B′

    module _ ds j y Γ₀ t B i where
      ℍ[16] : Type
      ℍ[16] =
          let
            xs = map (proj₂ ∘ proj₂) ds
            A  = proj₁ (ds ‼ j)
            j′ = ‼-map {xs = ds} j
            Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
            Γ  = Δ ∣ Γ₀
            Γₜ = Γ at t
          in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → ∃ λ (fresh-y : y ∉ ids Γ₀)
        → let
            α   = auth-destroy⦅ A , xs , j′ ⦆
            Γ′  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-AuthDestroy] fresh-y) refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₁₆ {Rˢ} 𝕣 t α t′ ds Γ₀  j A y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
          in
          ∃ λ (T : Tx i 0)
        → ((hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T))
        × ∃ λ (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ T ♯ ]) (toList Rᶜ))
        → let
            m = [ SIG (K̂ A) T ]
            λᶜ = B →∗∶ m
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m) (Any-tail T∈)
        × (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
            → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
            → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))
        × (A₀ ≡ B)
        × (m₀ ≡ m)

      ℍ[16]? : Dec ℍ[16]
      ℍ[16]? = {!!}

    ∃ℍ[16] = ∃ λ ds → ∃ λ j → ∃ λ y → ∃ λ Γ₀ → ∃ λ t → ∃ λ B → ∃ λ i →
      ℍ[16] ds j y Γ₀ t B i
-}

    data DecodeBroadcastResponse : Type where

      [1] : ∀ ⟨G⟩C →

        ℍ[1] ⟨G⟩C
        ───────────────────────
        DecodeBroadcastResponse

      [2] : ∀ ⟨G⟩C Δ×h̅ (k⃗ : 𝕂²′ ⟨G⟩C) A Γ₀ t →

        ℍ[2] ⟨G⟩C Δ×h̅ k⃗ A Γ₀ t
        ───────────────────────
        DecodeBroadcastResponse

      [3] : ∀ ⟨G⟩C Γ₀ t A v x →

        ℍ[3] ⟨G⟩C Γ₀ t A v x
        ───────────────────────
        DecodeBroadcastResponse
{-
      [5] : ∀ A v x Γ₀ t c (i : Index c) →

        ℍ[5] A v x Γ₀ t c i
        ────────────────────────
        DecodeBroadcastResponse

      [7] : ∀ ⟨G⟩C A a n Γ₀ t Δ×h̅ (k⃗ : 𝕂²′ ⟨G⟩C) →

        ℍ[7] ⟨G⟩C A a n Γ₀ t Δ×h̅ k⃗
        ───────────────────────────
        DecodeBroadcastResponse

      [10] : ∀ A v x v′ x′ Γ₀ t →

        ℍ[10] A v x v′ x′ Γ₀ t
        ───────────────────────
        DecodeBroadcastResponse

      [12] : ∀ A v v′ x Γ₀ t →

        ℍ[12] A v v′ x Γ₀ t
        ───────────────────────
        DecodeBroadcastResponse

      [14] : ∀ A v x Γ₀ t B′ →

        ℍ[14] A v x Γ₀ t B′
        ───────────────────────
        DecodeBroadcastResponse

      [16] : ∀ ds (j : Index ds) y Γ₀ t B i →

        ℍ[16] ds j y Γ₀ t B i
        ───────────────────────
        DecodeBroadcastResponse
-}
      FAIL :
        let λᶜ = A₀ →∗∶ m₀ in

        (∀ {Γₜ} (λˢ : 𝕃 Rˢ Γₜ) → (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ≁₁ (λᶜ ∷ Rᶜ ✓))
        ─────────────────────────────────────────────────────────
        DecodeBroadcastResponse

    try-decode-[1] : Dec ∃ℍ[1]
    try-decode-[1]
      with try-decode {Rˢ = Rˢ} 𝕣∗ m₀
    ... | no m≢ = no λ (_ , _ , _ , _ , m≡) → m≢ (_ , m≡)
    ... | yes (⟨G⟩C , m≡)
      with ℍ[1]? ⟨G⟩C
    ... | yes h = yes (-, h)
    ... | no ¬[1] = no go
      where
        go : ¬ ∃ℍ[1]
        go (_ , h@(_ , _ , _ , m≡′))
          rewrite encode-injective 𝕣 {ad = ⟨G⟩C} (trans (sym m≡) m≡′)
          = ¬[1] h

    try-decode-[2] : Dec ∃ℍ[2]
    try-decode-[2] = {!!}

    try-decode-[3] : Dec ∃ℍ[3]
    try-decode-[3] = {!!}
{-
    try-decode-[5] : Dec ∃ℍ[5]
    try-decode-[5] = {!!}

    try-decode-[7] : Dec ∃ℍ[7]
    try-decode-[7] = {!!}

    try-decode-[10] : Dec ∃ℍ[10]
    try-decode-[10] = {!!}

    try-decode-[12] : Dec ∃ℍ[12]
    try-decode-[12] = {!!}

    try-decode-[14] : Dec ∃ℍ[14]
    try-decode-[14] = {!!}

    try-decode-[16] : Dec ∃ℍ[16]
    try-decode-[16] = {!!}
-}
    decodeBroadcast : DecodeBroadcastResponse
    decodeBroadcast
      with try-decode-[1]
    ... | yes (⟨G⟩C , h) = [1] ⟨G⟩C h
    ... | no ¬[1]
      with try-decode-[2]
    ... | yes (⟨G⟩C , Δ×h̅ , k⃗ , A , Γ₀ , t , h) = [2] ⟨G⟩C Δ×h̅ k⃗ A Γ₀ t h
    ... | no ¬[2]
      with try-decode-[3]
    ... | yes (⟨G⟩C , Γ₀ , t , A , v , x , h) = [3] ⟨G⟩C Γ₀ t A v x h
    ... | no ¬[3]
{-
      with try-decode-[5]
    ... | yes (A , v , x , Γ₀ , t , c , i , h) = [5] A v x Γ₀ t c i h
    ... | no ¬[5]
      with try-decode-[7]
    ... | yes (⟨G⟩C , A , a , n , Γ₀ , t , Δ×h , k⃗ , h) = [7] ⟨G⟩C A a n Γ₀ t Δ×h k⃗ h
    ... | no ¬[7]
      with try-decode-[10]
    ... | yes (A , v , x , v′ , x′ , Γ₀ , t , h) = [10] A v x v′ x′ Γ₀ t h
    ... | no ¬[10]
      with try-decode-[12]
    ... | yes (A , v , v′ , x , Γ₀  , t , h) = [12] A v v′ x Γ₀ t h
    ... | no ¬[12]
      with try-decode-[14]
    ... | yes (A , v , x , Γ₀ , t , B′ , h) = [14] A v x Γ₀ t B′ h
    ... | no ¬[14]
      with try-decode-[16]
    ... | yes (ds , j , y , Γ₀ , t , B , i , h) = [16] ds j y Γ₀ t B i h
    ... | no ¬[16]
-}
      = FAIL go
      where
        go : ∀ {Γₜ} (λˢ : 𝕃 Rˢ Γₜ) →
          (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ≁₁ ((A₀ →∗∶ m₀) ∷ Rᶜ ✓)
        go = {!!}
      {-
        go _
          ([L] [1] {⟨G⟩C = ⟨G⟩C} {Γ = Γ} R≈ ∃Γ≈ vad hon d⊆)
          = ¬[1] (_ , vad , hon , d⊆′ , refl)
          where
            d⊆′ : ⟨G⟩C ⊆⦅ deposits ⦆ (Rˢ ∙cfg)
            d⊆′ = ∈deposits-resp-≈ _ {Γ}{Rˢ ∙cfg} (↭-sym $ R≈ .proj₂) ∘ d⊆
        go _
          ([L] [2] {⟨G⟩C = ⟨G⟩C} {Γ₀ = Γ₀} {t = t} {A = A} {Δ×h̅ = Δ×h̅} {k⃗ = k⃗}
                   R≈ ∃Γ≈ as≡ All∉ Hon⇒ ∃B h≡ h∈O unique-h h♯sechash)
          = ¬[2] ( ⟨G⟩C , Δ×h̅ , k⃗ , A , Γ₀ , t
                 , R≈ , as≡ , All∉ , Hon⇒ , ∃B , h≡ , h∈O , unique-h , h♯sechash , refl )
        -- go _
        --   ([L] [3] {⟨G⟩C = ⟨G⟩C} {Γ₀ = Γ₀} {t = t} {A = A} {x = x} {v = v}
        --            R≈ ∃Γ≈ committedA A∈per ∃B)
        --   = ¬[3] (⟨G⟩C , Γ₀ , t , A , v , x , R≈ , committedA , A∈per , ∃B , refl)
        -- go _ ([L] [5] ⋯) = ¬[5] ⋯
        -- ⋮
        go _ _ = {!!}
      -}

  module _ (T₀ : ∃Tx) where

    module _ (⟨G⟩C : Ad) z Γ₀ t where

      ℍ[4] : Type
      ℍ[4] =
          let
            ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG
            toSpend = persistentDeposits G
            vs      = map select₂ toSpend
            xs      = map select₃ toSpend
            v       = sum vs

            Γ = ` ⟨G⟩C ∣ Γ₀
              ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ⟨G⟩C ] }) toSpend
              ∣ || map (_auth[ ♯▷ ⟨G⟩C ]) partG
            Γₜ = Γ at t
          in
        ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = init⦅ G , C ⦆
            Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
        ∃ λ (fresh-z : z ∉ xs ++ ids Γ₀)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([C-Init] fresh-z) refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₄ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ toSpend v z R≈ Γ→Γ′ ∃Γ≈ using (T)
          in
          T₀ ≡ T

      ℍ[4]? : Dec ℍ[4]
      ℍ[4]? = {!!}
      {-
          let
            ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG
            toSpend = persistentDeposits G
            vs      = map select₂ toSpend
            xs      = map select₃ toSpend
            v       = sum vs

            Γ = ` ⟨G⟩C ∣ Γ₀
              ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ⟨G⟩C ] }) toSpend
              ∣ || map (_auth[ ♯▷ ⟨G⟩C ]) partG
            Γₜ = Γ at t
          in
        ((Rˢ .end .time ≟ t) ×-dec ((Rˢ ∙cfg) ≈? Γ)) ∃-dec λ R≈
        → let
            α   = init⦅ G , C ⦆
            Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
        (z ∉? xs ++ ids Γ₀) ∃-dec λ fresh-z
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([C-Init] fresh-z) refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₄ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ toSpend v z R≈ Γ→Γ′ ∃Γ≈ using (T)
          in
          T₀ ≟ T
      -}
    ∃ℍ[4] = ∃ λ ⟨G⟩C → ∃ λ z → ∃ λ Γ₀ → ∃ λ t →
      ℍ[4] ⟨G⟩C z Γ₀ t
{-
    module _ c (i : Index c) (ds : List (Participant × S.Value × Id)) (ss : List (Participant × Secret × ℕ)) v y p c′ y′ Γ₀ t where

      ℍ[6] : Type
      ℍ[6] = let open ∣SELECT c i; As , ts = decorations d in
          let
            -- (i) xs = x₁⋯xₖ
            (_ , vs , xs) = unzip₃ ds
            (_ , as , _)  = unzip₃ ss
            Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
            Δ   = || map (uncurry₃ _∶_♯_) ss
            Γ₂  = Δ ∣ Γ₀
            Γ₁₂ = Γ₁ ∣ Γ₂
            Γ   = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₂)
            Γₜ  = Γ at t
          in
          ∃ λ (t≡ : t ≡ maximum t ts)
        → ∃ λ (d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′)
        → ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = put⦅ xs , as , y ⦆
            Γ′  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          ∃ λ (fresh-y′ : y′ ∉ y L.∷ ids Γ₁₂)
        → ∃ λ (p⟦Δ⟧≡ : ⟦ p ⟧ᵖ Δ ≡ just true)
        → ∃ λ (As≡∅ : Null As)
        → let
            ∀≤t : All (_≤ t′) ts
            ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

            put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
            put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡
                ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Timeout] As≡∅ ∀≤t put→ refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₆ {Rˢ} 𝕣 t α t′ c v y ds ss Γ₂ c′ y′ i p R≈ Γ→Γ′ ∃Γ≈ d≡ using (T)
          in
          T₀ ≡ T

      ℍ[6]? : Dec ℍ[6]
      ℍ[6]? = {!!}

    ∃ℍ[6] = ∃ λ c → ∃ λ i → ∃ λ ds → ∃ λ ss → ∃ λ v → ∃ λ y → ∃ λ p → ∃ λ c′ → ∃ λ y′ → ∃ λ Γ₀ → ∃ λ t →
      ℍ[6] c i ds ss v y p c′ y′ Γ₀ t

    module _ c (i : Index c) (vcis : List (S.Value × Contracts × Id)) y Γ₀ t where

      ℍ[8] : Type
      ℍ[8] =
          let open ∣SELECT c i; As , ts = decorations d in
          let vs , cs , xs = unzip₃ vcis; v = sum vs in
          let Γ = ⟨ c , v ⟩at y ∣ Γ₀; Γₜ = Γ at t in

          ∃ λ (t≡ : t ≡ maximum t ts)
        → ∃ λ (d≡ : d ≡⋯∶ split (zip vs cs))
        → ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → ∃ λ (fresh-xs : All (_∉ y L.∷ ids Γ₀) xs)
        → ∃ λ (As≡∅ : Null As)
        → let
            α   = split⦅ y ⦆
            Γ′  = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′

            ∀≤t : All (_≤ t′) ts
            ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

            split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
            split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
                  ~: [C-Split] {vcis = vcis} fresh-xs

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Timeout] As≡∅ ∀≤t split→ refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₈ {Rˢ} 𝕣 t α t′ c v y Γ₀ i vcis R≈ Γ→Γ′ ∃Γ≈ d≡ using (T)
          in
          T₀ ≡ T

      ℍ[8]? : Dec ℍ[8]
      ℍ[8]? = {!!}

    ∃ℍ[8] = ∃ λ c → ∃ λ i → ∃ λ vcis → ∃ λ y → ∃ λ Γ₀ → ∃ λ t →
      ℍ[8] c i vcis y Γ₀ t

    module _ c (i : Index c) v y A x Γ₀ t where

      ℍ[9] : Type
      ℍ[9] =
        let open ∣SELECT c i; As , ts = decorations d in
        let Γ = ⟨ c , v ⟩at y ∣ Γ₀; Γₜ = Γ at t in

          ∃ λ (d≡ : d ≡⋯∶ withdraw A)
        → ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = withdraw⦅ A , v , y ⦆
            Γ′  = ⟨ A has v ⟩at x ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          ∃ λ (fresh-x : x ∉ y L.∷ ids Γ₀)
        → ∃ λ (As≡∅ : Null As)
        → ∃ λ (∀≤t : All (_≤ t) ts)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Timeout] As≡∅ ∀≤t
              (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x)
              refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₉ {Rˢ} 𝕣 t α t′ c v y Γ₀ A x i R≈ Γ→Γ′ ∃Γ≈ d≡ using (T)
          in
          T₀ ≡ T

      ℍ[9]? : Dec ℍ[9]
      ℍ[9]? = {!!}

    ∃ℍ[9] = ∃ λ c → ∃ λ i → ∃ λ v → ∃ λ y → ∃ λ A → ∃ λ x → ∃ λ Γ₀ → ∃ λ t →
      ℍ[9] c i v y A x Γ₀ t

    module _ A v x v′ x′ y Γ₀ t where

      ℍ[11] : Type
      ℍ[11] =
          let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = join⦅ x ↔ x′ ⦆
            Γ′  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          ∃ λ (fresh-y : y ∉ x L.∷ x′ ∷ ids Γ₀)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-Join] fresh-y) refl

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
            x∈′ = n⊆ (there $′ here refl)

            T : ∃Tx
            T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
              { inputs  = hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ []
              ; wit     = wit⊥
              ; relLock = V.replicate 0
              ; outputs = [ (v + v′) -redeemableWith- K̂ A ]
              ; absLock = 0 }
          in
          T₀ ≡ T

      ℍ[11]? : Dec ℍ[11]
      ℍ[11]? = {!!}

    ∃ℍ[11] = ∃ λ A → ∃ λ v → ∃ λ x → ∃ λ v′ → ∃ λ x′ → ∃ λ y → ∃ λ Γ₀ → ∃ λ t →
      ℍ[11] A v x v′ x′ y Γ₀ t

    module _ A v v′ x y y′ Γ₀ t where

      ℍ[13] : Type
      ℍ[13] =
          let Γ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = divide⦅ x ▷ v , v′ ⦆
            Γ′  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          ∃ λ (fresh-ys : All (_∉ x L.∷ ids Γ₀ ) (y ∷ y′ ∷ []))
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-Divide] fresh-ys) refl

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)

            T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
              { inputs  = [ hashTxⁱ (txout′ {x} x∈) ]
              ; wit     = wit⊥
              ; relLock = V.replicate 0
              ; outputs = (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ []
              ; absLock = 0 }
          in
          T₀ ≡ T

      ℍ[13]? : Dec ℍ[13]
      ℍ[13]? = {!!}

    ∃ℍ[13] = ∃ λ A → ∃ λ v → ∃ λ v′ → ∃ λ x → ∃ λ y → ∃ λ y′ → ∃ λ Γ₀ → ∃ λ t →
      ℍ[13] A v v′ x y y′ Γ₀ t

    module _ A v x B′ y Γ₀ t where

      ℍ[15] : Type
      ℍ[15] =
          let Γ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀; Γₜ = Γ at t in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = donate⦅ x ▷ᵈ B′ ⦆
            Γ′  = ⟨ B′ has v ⟩at y ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          ∃ λ (fresh-y : y ∉ x L.∷ ids Γ₀)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-Donate] fresh-y) refl

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)

            T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
              { inputs  = [ hashTxⁱ (txout′ {x} x∈) ]
              ; wit     = wit⊥
              ; relLock = V.replicate 0
              ; outputs = [ v -redeemableWith- K̂ B′ ]
              ; absLock = 0 }
          in
          T₀ ≡ T

      ℍ[15]? : Dec ℍ[15]
      ℍ[15]? = {!!}

    ∃ℍ[15] = ∃ λ A → ∃ λ v → ∃ λ x → ∃ λ B′ → ∃ λ y → ∃ λ Γ₀ → ∃ λ t →
      ℍ[15] A v x B′ y Γ₀ t

    module _ ds (j : Index ds) y Γ₀ t i where

      ℍ[17] : Type
      ℍ[17] =
          let
            xs = map (proj₂ ∘ proj₂) ds
            Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                        (enumerate ds)
            Γ  = Δ ∣ Γ₀
            Γₜ = Γ at t
          in
          ∃ λ (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = destroy⦅ xs ⦆
            Γ′  = Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] [DEP-Destroy] refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₁₇ {Rˢ} 𝕣 t α t′ ds Γ₀ y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
          in
          ∃ λ (T : Tx i 0)
        → ((hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T))
        × ( let λᶜ = submit (-, -, T) in
          ∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
            → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
            → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))
        × (T₀ ≡ (-, -, T))

      ℍ[17]? : Dec ℍ[17]
      ℍ[17]? = {!!}

    ∃ℍ[17] = ∃ λ ds → ∃ λ j → ∃ λ y → ∃ λ Γ₀ → ∃ λ t → ∃ λ i →
      ℍ[17] ds j y Γ₀ t i
-}
    data DecodeTxResponse : Type where

      [4] : ∀ ⟨G⟩C z Γ₀ t →

        ℍ[4] ⟨G⟩C z Γ₀ t
        ────────────────
        DecodeTxResponse
{-
      [6] : ∀ c (i : Index c) ds ss v y p c′ y′ Γ₀ t →

        ℍ[6] c i ds ss v y p c′ y′ Γ₀ t
        ───────────────────────────────
        DecodeTxResponse

      [8] : ∀ c (i : Index c) vcis y Γ₀ t →

        ℍ[8] c i vcis y Γ₀ t
        ────────────────────
        DecodeTxResponse

      [9] : ∀ c (i : Index c) v y A x Γ₀ t →

        ℍ[9] c i v y A x Γ₀ t
        ─────────────────────
        DecodeTxResponse

      [11] : ∀ A v x v′ x′ y Γ₀ t →

        ℍ[11] A v x v′ x′ y Γ₀ t
        ────────────────────────
        DecodeTxResponse

      [13] : ∀ A v v′ x y y′ Γ₀ t →

        ℍ[13] A v v′ x y y′ Γ₀ t
        ────────────────────────
        DecodeTxResponse

      [15] : ∀ A v x B′ y Γ₀ t →

        ℍ[15] A v x B′ y Γ₀ t
        ─────────────────────
        DecodeTxResponse

      [17] : ∀ ds (j : Index ds) y Γ₀ t i →

        ℍ[17] ds j y Γ₀ t i
        ───────────────────
        DecodeTxResponse
-}
      FAIL :
        T₀ .proj₂ .proj₂ .inputs ♯ (hashTxⁱ <$> codom txout′)
        ─────────────────────────────────────────────────────
        DecodeTxResponse

    postulate MAGIC : ∃Tx → Maybe (Ad × Id × Cfg × S.Time)

    try-decode-[4] : Dec ∃ℍ[4]
    try-decode-[4]
      with MAGIC T₀
    ... | nothing = no {!!}
    ... | just (⟨G⟩C , z , Γ₀ , t)
      with ℍ[4]? ⟨G⟩C z Γ₀ t
    ... | yes h = yes (⟨G⟩C , z , Γ₀ , t , h)
    ... | no ¬[4] = no go
      where
        go : ¬ ∃ℍ[4]
        go (⟨G⟩C , z , Γ₀ , t , h@(_ , _ , T≡))
          = {!!}
          -- = ¬[4] h
{-
    try-decode-[6] : Dec ∃ℍ[6]
    try-decode-[6] = {!!}

    try-decode-[8] : Dec ∃ℍ[8]
    try-decode-[8] = {!!}

    try-decode-[9] : Dec ∃ℍ[9]
    try-decode-[9] = {!!}

    try-decode-[11] : Dec ∃ℍ[11]
    try-decode-[11] = {!!}

    try-decode-[13] : Dec ∃ℍ[13]
    try-decode-[13] = {!!}

    try-decode-[15] : Dec ∃ℍ[15]
    try-decode-[15] = {!!}

    try-decode-[17] : Dec ∃ℍ[17]
    try-decode-[17] = {!!}
-}
    decodeTx : DecodeTxResponse
    decodeTx
      with try-decode-[4]
    ... | yes (⟨G⟩C , z , Γ₀ , t , h)
        = [4] ⟨G⟩C z Γ₀ t h
    ... | no ¬[4]
{-
      with try-decode-[6]
    ... | yes (c , i , ds , ss , v , y , p , c′ , y′ , Γ₀ , t , h)
        = [6] c i ds ss v y p c′ y′ Γ₀ t h
    ... | no ¬[6]
      with try-decode-[8]
    ... | yes (c , i , vcis , y , Γ₀ , t , h)
        = [8] c i vcis y Γ₀ t h
    ... | no ¬[8]
      with try-decode-[9]
    ... | yes (c , i , v , y , A , x , Γ₀ , t , h)
        = [9] c i v y A x Γ₀ t h
    ... | no ¬[9]
      with try-decode-[11]
    ... | yes (A , v , x , v′ , x′ , y , Γ₀ , t , h)
        = [11] A v x v′ x′ y Γ₀ t h
    ... | no ¬[11]
      with try-decode-[13]
    ... | yes (A , v , v′ , x , y , y′ , Γ₀ , t , h)
        = [13] A v v′ x y y′ Γ₀ t h
    ... | no ¬[13]
      with try-decode-[15]
    ... | yes (A , v , x , B′ , y , Γ₀ , t , h)
        = [15] A v x B′ y Γ₀ t h
    ... | no ¬[15]
      with try-decode-[17]
    ... | yes (ds , j , y , Γ₀ , t , i , h)
        = [17] ds j y Γ₀ t i h
    ... | no ¬[17]
-}
      = FAIL ins♯
      where
        -- [T0D0] What happens when T consumes inputs from txout′, but does not correspond to any case?
        ins♯ : T₀ .proj₂ .proj₂ .inputs ♯ (hashTxⁱ <$> codom txout′)
        ins♯ = {!!}
-}
