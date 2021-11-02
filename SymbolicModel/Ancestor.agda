module SymbolicModel.Ancestor where

{-

-- ** ancestor advertisement of an active contract

Ancestor : Run → ActiveContract → Advertisement → Set
Ancestor R (c , v , x) ad
  = (c ⊆ subtermsᶜ′ (C ad))
  × (ad ∈ advertisements R)
  × Any ((` ad) ∈ᶜ_) Rᶜ
  × Any (⟨ c , v ⟩at x ∈ᶜ_) Rᶜ
  where Rᶜ = allCfgs R

Ancestor⇒∈ : Ancestor R (c , v , x) ad → c ⊆ subtermsᶜ′ (C ad)
Ancestor⇒∈ = proj₁

Ancestor→𝕂 : Ancestor R (c , v , x) ad → ad ∈ advertisements R
Ancestor→𝕂 = proj₁ ∘ proj₂

-- T0D0: replace with SymbolicModel.Ancestor, with proper provenance

-}

{-
Ancestor : Run → ActiveContract → Advertisement → Set
Ancestor R (c , v , x) ad
  = (c ⊆ subtermsᶜ′ (C ad))
  × (ad ∈ advertisements R)
  × Any ((` ad) ∈ᶜ_) Rᶜ
  × Any (⟨ c , v ⟩at x ∈ᶜ_) Rᶜ
  where Rᶜ = allCfgs R

Ancestor⇒∈ : Ancestor R (c , v , x) ad → c ⊆ subtermsᶜ′ (C ad)
Ancestor⇒∈ = proj₁

Ancestor→𝕂 : Ancestor R (c , v , x) ad → ad ∈ advertisements R
Ancestor→𝕂 = proj₁ ∘ proj₂
-}

-- transitions inside a symbolic run
-- Transition a = a × Label × a
-- TransitionList = List ∘ Transition

-- transitionsᵗ : Run → TransitionList TimeConfiguration
-- transitionsᵗ (_ ∙) = []
-- transitionsᵗ (tc ∷⟦ α ⟧ R) = (tc , α , lastCfgᵗ R) ∷ transitionsᵗ R

-- transitions : Run → TransitionList Configuration
-- transitions (_ ∙) = []
-- transitions (tc ∷⟦ α ⟧ R) = (cfg tc , α , cfg $ lastCfgᵗ R) ∷ transitions R

-- lifetime of a contract

-- private variable ts : List ActiveContract

-- data ℝ : Run → Contracts → Advertiment → Set where

--   → ` ad ∈ᶜ Γ
--     -------------
--   → ℝ R (C ad) ad

-- T0D0
-- reuse InferenceRules via Γ —→⟨ α ⟩ Γ′ (possible reasoning up to permutation with _≈_ as well)
-- instead of defining another inductive datatype
-- data ℝ : Run → List ActiveContract → Advertisement → Set where

--   -- base : ℝ (Γₜ ∙) [] ad

--   advertise : let Γ = cfg (lastCfgᵗ R) in
--       ` ad ∈ᶜ Γ′
--       ---------------------------------
--     → ℝ (Γₜ ∷⟦ advertise[ ad ] ⟧ R) [] ad

--   -- advertise : let Γ = cfg Γₜ in
--   --     ` ad ∈ᶜ cfg Γₜ
--   --     ---------------------------------
--   --   → ℝ (Γₜ ∙) [] ad

--   other :
--       ℝ R ts ad
--       ---------------------
--     → ℝ (Γₜ ∷⟦ α ⟧ R) ts ad

--   init : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ; ⟨ G ⟩ C = ad in

--       ℝ R [] ad
--     → ` ad ∈ᶜ Γ
--     → ⟨ C , v ⟩at x ∈ᶜ Γ′
--       ---------------------------------------------------
--     → ℝ (Γₜ ∷⟦ init[ G , C ] ⟧ R) [(C , v , x)] ad

--   auth-control : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ in

--     --   ℝ R ts ad
--     -- → ⟨ ds , v ⟩at x ∈ᶜ Γ
--     -- → ⟨ ds , v ⟩at x ∈ᶜ Γ′
--     -- → d ∈ ds
--     --   --------------------------------------------------------------
--     -- → ℝ (Γₜ ∷⟦ auth-control[ A , x ▷ d ] ⟧ R) ((ds , v , x) ∷ ts) ad

--       ℝ R ts ad
--       --------------------------------------------------------------
--     → ℝ (Γₜ ∷⟦ auth-control[ A , x ▷ d ] ⟧ R) ts ad

--   split : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ in

--       ℝ R ts ad
--     → ⟨ ds , v ⟩at y ∈ᶜ Γ
--     → split vcs ∈ ds
--     → ⟨ c , v ⟩at x ∈ᶜ Γ′
--     → c ∈ map proj₂ vcs
--       ----------------------------------------------
--     → ℝ (Γₜ ∷⟦ split[ y ] ⟧ R) ((c , v , x) ∷ ts) ad

--   put : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ in

--       ℝ R ts ad
--     → ⟨ ds , v ⟩at y ∈ᶜ Γ
--     → (put xs &reveal as if p ⇒ c) ∈ ds
--     → ⟨ c , v′ ⟩at z ∈ᶜ Γ′
--       -------------------------------------------------------
--     → ℝ (Γₜ ∷⟦ put[ xs , as , y ] ⟧ R) ((c , v′ , z) ∷ ts) ad

{- T0D0: properly define ancestor/provenance
data ℝ : Run → List ActiveContract → Advertisement → Set where

  advertise : let Γ = cfg (lastCfgᵗ R) in
      ` ad ∈ᶜ Γ′
      ---------------------------------
    → ℝ (Γₜ ∷⟦ advertise[ ad ] ⟧ R) [] ad

  other :
      ℝ R ts ad
      ---------------------
    → ℝ (Γₜ ∷⟦ α ⟧ R) ts ad

  init : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ; ⟨ G ⟩ C = ad in

      ℝ R [] ad
    → ⟨ C , v ⟩at x ∈ᶜ Γ′
      ---------------------------------------------------
    → ℝ (Γₜ ∷⟦ init[ G , C ] ⟧ R) [(C , v , x)] ad

  auth-control : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ in

    --   ℝ R ts ad
    -- → ⟨ ds , v ⟩at x ∈ᶜ Γ
    -- → ⟨ ds , v ⟩at x ∈ᶜ Γ′
    -- → d ∈ ds
    --   --------------------------------------------------------------
    -- → ℝ (Γₜ ∷⟦ auth-control[ A , x ▷ d ] ⟧ R) ((ds , v , x) ∷ ts) ad

      ℝ R ts ad
    → Any (d ∈_) (map proj₁ ts)
      --------------------------------------------------------------
    → ℝ (Γₜ ∷⟦ auth-control[ A , x ▷ d ] ⟧ R) ts ad

  split : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ in

      ℝ R ts ad
    → ds ∈ map proj₁ ts
    → split vcs ∈ ds
    → ⟨ c , v ⟩at x ∈ᶜ Γ′
    → c ∈ map proj₂ vcs
      ----------------------------------------------
    → ℝ (Γₜ ∷⟦ split[ y ] ⟧ R) ((c , v , x) ∷ ts) ad

  put : let Γ = cfg (lastCfgᵗ R); Γ′ = cfg Γₜ in

      ℝ R ts ad
    → ds ∈ map proj₁ ts
    → (put xs &reveal as if p ⇒ c) ∈ ds
    → ⟨ c , v′ ⟩at z ∈ᶜ Γ′
      -------------------------------------------------------
    → ℝ (Γₜ ∷⟦ put[ xs , as , y ] ⟧ R) ((c , v′ , z) ∷ ts) ad

-- Lifetime : Run → ActiveContract → Advertisement × List ActiveContract → Set
-- Lifetime R (c , v , x) (ad@(⟨ G ⟩ C) , ts) = ?
-}

{-
Ancestor R c ad = ∃[ ts ] ℝ R (c ∷ ts) ad
  -- Any (λ{ ((Γ at _) , α , (Γ′ at _)) → (α ≡ init[ G , C ]) × ( ` ad ∈ᶜ Γ ) × ( ⟨ C , v ⟩at x ∈ᶜ Γ′ )})
  --     (transitions R)


private variable ac : ActiveContract

-- _ :
--   → ℝ R ts ad
--   → All (λ c → Any (c ∈ᶜ_) (cfgs R)) (map proj₁ ts)

-- ℝ⇒ :
--     ℝ R ts ad
--   → ⟨ ds , v ⟩at x ∈ᶜ cfg (lastCfgᵗ R)
--   -- → ds ∈ map proj₁ ts
--   → ds ⊆ subtermsᶜ′ (C ad)
-- ℝ⇒ (advertise x) ds∈ = {!!}
-- ℝ⇒ (other p) ds∈ = {!!}
-- ℝ⇒ (init p x x₁) ds∈ = {!!}
-- ℝ⇒ (auth-control p) ds∈ = {!!}
-- ℝ⇒ (split p x x₁ x₂ x₃) ds∈ = {!!}
-- ℝ⇒ (put p x x₁ x₂) ds∈ = {!!}

ℝ⇒∈ :
    ℝ R ts ad
  → c ∈ map proj₁ ts
  → c ⊆ subtermsᶜ′ (C ad)
ℝ⇒∈ (other p) c∈ = ℝ⇒∈ p c∈
ℝ⇒∈ (init _ _) (here refl) = subterms⊆ᶜˢ
ℝ⇒∈ (auth-control p _) c∈ = ℝ⇒∈ p c∈
ℝ⇒∈ {ts = ((c , v , x) ∷ ts)} {ad = ad} (split {ds = ds} {y = y′} p pre ∈ds post c∈) (here refl)
  = qed
  where
  -- p : ℝ R ts ad
  -- ~> p′ : ds ⊆ subtermsᶜ′ (C ad)
    pp : ds ⊆ subtermsᶜ′ (C ad)
    pp = ℝ⇒∈ {c = ds} p pre
  -- pre : ds ∈ map proj₁ ts
  -- ∈ds : split vcs ∈ ds
    ∈ds′ : split vcs ∈ subtermsᶜ′ ds
    ∈ds′ = {!!}
  -- ~> ∈ds′ : split vcs ∈ subtermsᶜ′ ds
  -- post : ⟨ c , v ⟩at x′ ∈ᶜ cfg Γₜ
  -- c∈ : c ∈ map proj₂ vcs
  -- ~> c∈′ : c ∈ subtermsᵈ′ (split vcs)
    c∈′ : c ⊆ subtermsᵈ′ (split vcs)
    c∈′ = {!!}
  -- ~~> c∈″ : c ∈ subtermsᶜ′ ds
    c∈″ : c ⊆ subtermsᶜ′ ds
    c∈″ = {!!}
  -- ————————————————————————————————
  -- qed : c ⊆ subtermsᶜ′ (C ad)
    qed : c ⊆ subtermsᶜ′ (C ad)
    qed = {!!} -- subtermsᶜ′-trans pp -- c∈″

ℝ⇒∈ {ts = .((_ , _ , _) ∷ _)} (split p x x₁ x₂ x₃) (there y) = {!!}

-- ℝ⇒∈ {ts = ts} (split p x x₁ x₂ x₃) (here refl) =
--   {!!}

  -- ℝ⇒∈ p {!here refl!}
  -- where
  --   qed : c ∈ map proj₁ ts
  --   qed = ?

    -- p : ℝ R ts ad

-- ℝ⇒∈ (split p x x₁ x₂ x₃) (there c∈) = ℝ⇒∈ p c∈
ℝ⇒∈ (put p x x₁ x₂) c∈ = {!ℝ⇒∈ p c∈!}

-}

-- Ancestor⇒∈ (ts , p) = ℝ⇒∈ p (here refl)

-- Ancestor⇒∈ (ts , other p) = Ancestor⇒∈ (ts , p)
-- Ancestor⇒∈ (.[] , init p x x₁) = subterms⊆ᶜˢ
-- Ancestor⇒∈ (ts , auth-control p) = Ancestor⇒∈ (ts , p)
-- Ancestor⇒∈ (ts , split p x x₁ x₂ x₃) = {!!}
-- Ancestor⇒∈ (ts , put p x x₁ x₂) = {!!}
