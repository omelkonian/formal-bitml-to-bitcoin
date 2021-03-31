------------------------------------------------------------------------
-- Lemmas related to BitML's symbolic model.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.List using (length; map; concatMap; _++_; zip)
open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets

open import BitML.BasicTypes

module SymbolicModel.Lemmas
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Strategy Participant Honest as SM

----------------------------------------
-- Lemma 3

module _ (α≢₁ : ∀ A s      → α ≢ auth-rev[ A , s ])
         (α≢₂ : ∀ A ⟨G⟩C Δ → α ≢ auth-commit[ A , ⟨G⟩C , Δ ]) where

  strip-preserves-semantics :
      ( ∀ T′ → R   ——→[ α ] T′
               --------------------
             → R ∗ ——→[ α ] T′ ∗ )

    × ( ∀ T′ → R ∗ ——→[ α ] T′
               --------------------------
             → ∃[ T″ ] ( (R ——→[ α ] T″)
                       × T′ ∗ ≡ T″ ∗ ))
  strip-preserves-semantics = {!!}

{-
  strip-preserves-semantics {R = R} = pr₁ , pr₂
    where
      strip-→ : Γ —→[ α ] Γ′
            ------------------------------------------------
          → Γ ∗ —→[ α ] Γ′ ∗
      strip-→ ([C-AuthRev] {s = s} {A = A} _)
        = ⊥-elim (α≢₁ A s refl)
      strip-→ ([C-AuthCommit] {A = A} {ci = ci} {pi = pi} {ad = ad} {secrets = secrets}  _ _)
        = ⊥-elim (α≢₂ A (ci , pi , ad) secrets refl)

      strip-→ [C-Withdraw]          = [C-Withdraw]
      strip-→ ([C-AuthControl] x)   = [C-AuthControl] x
      strip-→ [DEP-AuthJoin]        = [DEP-AuthJoin]
      strip-→ [DEP-Join]            = [DEP-Join]
      strip-→ [DEP-AuthDivide]      = [DEP-AuthDivide]
      strip-→ [DEP-Divide]          = [DEP-Divide]
      strip-→ [DEP-AuthDonate]      = [DEP-AuthDonate]
      strip-→ [DEP-Donate]          = [DEP-Donate]
      strip-→ [DEP-AuthDestroy]     = [DEP-AuthDestroy]
      strip-→ [DEP-Destroy]         = [DEP-Destroy]
      strip-→ ([C-Advertise] x x₁)  = [C-Advertise] x x₁

      strip-→ ([C-AuthInit] {dsˡ = dsˡ} {dsʳ = dsʳ} {ad = ad} {Γ = Γ} {p = refl} x x₁) =
        [C-AuthInit] {dsˡ = dsˡ} {dsʳ = dsʳ} {p = refl} x (strip-committedParticipants₂ {Γp = Γ} {ad = ad} x₁)

      strip-→ ([C-Init] {ad = ad} {Δ = Δ} x x₁ x₂) =
        [C-Init] x (strip-committedParticipants₂ {Γp = Δ} {ad = ad} x₁)
                   (strip-spentForStipulation₂ {ad = ad} {Δ = Δ} x₂)

      strip-→ ([C-Split] {vs = vs} {Γ = Γ} {cases = cases} refl refl)
        rewrite strip-cases {cs′ = casesToContracts cases} {Γ = Γ}
              = [C-Split] refl refl

      strip-→ ([C-PutRev] {Γ = Γ} {ds′ = ds′} {Δ = ss} pr x x₁ x₂)
        rewrite strip-ds {ds′ = ds′} {Γ = V.toList ss ∣∣ˢˢ Γ}
              | strip-ss {ss = V.toList ss} {Γ = Γ}
              = [C-PutRev] {Γ = Γ ∗} {ds′ = ds′} {Δ = ss} pr x x₁ x₂

      strip-→ ([C-Control] {contract = c} {i = i})
        rewrite strip-b {Γ = ⟨ c ⟩ᶜ} {ps = authDecorations (c ‼ i)} {i = 0F} {j = i}
              = [C-Control]

      strip-→ₜ : Γ      at t —→ₜ[ α ] Γ′      at t′
               → (Γ ∗) at t —→ₜ[ α ] (Γ′ ∗) at t′
      strip-→ₜ ([Action] Γ→) = [Action] (strip-→ Γ→)
      strip-→ₜ [Delay]       = [Delay]
      strip-→ₜ {t = t} {t′ = t′} ([Timeout] {Γ = Γ} {Γ′ = Γ′} ∀≤t c‼i→)
          = [Timeout] {Γ = Γ ∗} {Γ′ = Γ′ ∗} ∀≤t (strip-→ c‼i→)

      pr₁ : ∀ T′
        → R   ——→[ α ] T′
          -----------------
        → R ∗ ——→[ α ] T′ ∗ᵗ
      pr₁ T′ R→ rewrite strip-lastCfg {R}
                      = strip-→ₜ R→

      pr0 : ∀ (Γ₀ : Configuration Iᶜᶠ[ ads , cs , ds ])
        → Γ₀ —→[ α ] Γ′
        → Γ₀ ≡ Γ ∗
          ---------------------------------
        → ∃[ Γ″ ] ( (Γ —→[ α ] Γ″)
                  × Γ′ ∗ ≡ Γ″ ∗ )
      pr0 {Γ′ = Γ′} {Γ = Γ} Γ₀ Γ→ Γ₀≡
        with Γ→
      ... | _ = {!!}
      -- ... | [C-AuthRev] {s = s} {A = A} _
      --     = ⊥-elim (α≢₁ A s refl)
      -- ... | [C-AuthCommit] {A = A} {ci = ci} {pi = pi} {ad = ad} {secrets = secrets} _ _
      --     = ⊥-elim (α≢₂ A (ci , pi , ad) secrets refl)
      -- ... | [C-Withdraw] {v = v} {A = A} {Γ = γ∗}
      --     = let l = ⟨ A , v ⟩ᵈ
      --       in case destruct-γ∗ {Γ = Γ} {Γ₀ = Γ₀} {l = ⟨ [ withdraw A ] ⟩ᶜ} {γ∗ = γ∗}
      --                           {pr = refl & refl & refl & refl & refl & refl}
      --                           Γ₀≡ refl
      --          of λ { (γ , refl , refl) →
      --                    (l ∣∣ γ ∶- refl & refl & refl & refl & refl & refl)
      --                  , [C-Withdraw] {v = v} {A = A} {Γ = γ}
      --                  , strip-strip-rewrite {l = l} {γ = γ} {pr = refl & refl & refl & refl & refl & refl} }
      -- ... | [C-AuthControl] {A = A} {Γ = γ∗} {ci = ci} {contract = c} {i = i} p
      --     = let l = ⟨ c  ⟩ᶜ ∣∣ A auth[ c ▷ᵇ i ]∶- refl & refl & refl & refl & refl & refl
      --                       ∶- refl & refl & refl & \\-same {[ ci , c ]} & refl & refl
      --           in case destruct-γ∗ {Γ = Γ} {Γ₀ = Γ₀} {l = ⟨ c ⟩ᶜ} {γ∗ = γ∗}
      --                               {pr = refl & refl & refl & refl & refl & refl}
      --                               Γ₀≡ refl
      --              of λ { (γ , refl , refl) →
      --                        (l ∣∣ γ ∶- refl & refl & refl & refl & refl & refl)
      --                      , [C-AuthControl] {A = A} {Γ = γ} {contract = c} {i = i} p
      --                      , strip-strip-rewrite {l = l} {γ = γ} {pr = refl & refl & refl & refl & refl & refl} }

      pr1 : ∀ {Γ₀ : Configuration Iᶜᶠ[ ads , cs , ds ]}
        → Γ₀ at t —→ₜ[ α ] Γ′ at t′
        → Γ₀ ≡ Γ ∗
          ------------------------------------
        → ∃[ Γ″ ] ( (Γ at t —→ₜ[ α ] Γ″ at t′)
                  × (Γ′ ∗ ≡ Γ″ ∗) )
      pr1 {Γ′ = Γ′} {Γ = Γ} {Γ₀ = Γ₀} Γ→ₜ Γ₀≡ with Γ→ₜ
      ... | [Action] Γ→
          = case pr0 {Γ′ = Γ′} {Γ = Γ} Γ₀ Γ→ Γ₀≡
            of λ { (Γ″ , Γ→Γ″ , Γ≡) → Γ″ , [Action] Γ→Γ″ , Γ≡ }
      ... | [Delay] {δ = δ} = case Γ₀≡ of λ { refl → Γ , [Delay] {δ = δ} , strip-idempotent Γ }
      ... | [Timeout] {Γ = γ∗} {Γ′ = .Γ′} {contract = c} {i = i} ∀t Γ→
        with destruct-γ∗ {Γ = Γ} {Γ₀ = Γ₀} {l = ⟨ c ⟩ᶜ} {γ∗ = γ∗}
                         {pr = refl & refl & refl & refl & refl & refl}
                         Γ₀≡ refl
      ... | γ , refl , refl
        with pr0 {Γ′ = Γ′}
                 {Γ = ⟨ [ c ‼ i ] ⟩ᶜ ∣∣ γ ∶- refl & refl & refl & refl & refl & refl}
                 (⟨ [ c ‼ i ] ⟩ᶜ ∣∣ γ∗ ∶- refl & refl & refl & refl & refl & refl)
                 Γ→ refl
      ... | Γ″ , Γ→Γ″ , Γ≡
          = Γ″ , [Timeout] {Γ = γ} {Γ′ = Γ″} {contract = c} {i = i} ∀t Γ→Γ″ , Γ≡

      pr₂ : ∀ T′
        → R ∗ ——→[ α ] T′
          --------------------------
        → ∃[ T″ ] ( (R ——→[ α ] T″)
                  × T′ ∗ᵗ ≡ T″ ∗ᵗ )
      pr₂ T′ R→
        with inspect (lastCfg R)
      ... | (cfi , tc) with≡ eq
        with inspect T′
      ... | (cfi′ , tc′) with≡ eq′
        with inspect tc
      ... | (Γ at t) with≡ eqt
        with inspect tc′
      ... | (Γ′ at t′) with≡ eqt′
        with (eq , eq′ , eqt , eqt′)
      ... | refl , refl , refl , refl
        with pr1 {t = t} {Γ′ = Γ′} {t′ = t′} {Γ = Γ} {Γ₀ = Γ ∗} (help {R = R} {T′ = T′} R→) refl
      ... | Γ″ , Γ→ , Γ≡ = (cfi′ , Γ″ at t′) , Γ→ , cong (λ g → (cfi′ , g at t′)) Γ≡
-}

----------------------------------------
-- Lemma 4

module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open SM.AdvM Adv Adv∉

  variable
    S† : AdversaryStrategy
    S  : HonestStrategies

  adversarial-move-is-semantic :
    ∃[ T′ ] ( R ——→[ runAdversary (S† , S) R ] T′)
  adversarial-move-is-semantic = {!!}

{-
  valid-hon-move : ∀ {A} (A∈ : A ∈ Hon)
    → runAdversary (S† , S) R ∈ concatMap proj₂ (runHonestAll (R ∗) S)
    → runAdversary (S† , S) R ∈ strategy (S A∈) (R ∗)
  valid-hon-move = {!!}

  adversarial-move-is-semantic {R = R} {S† = S†} {S = S} =
    let
      moves = runHonestAll (R ∗) S
      (cases , v) = valid S† {R = R} {moves = moves}
    in case cases of
    λ { (inj₁ (A , A∈ , eq , α∈ ))
      → let (_ , R→ , _) = valid (S A∈)
        in R→ {R} {runAdversary (S† , S) R} (valid-hon-move {S† = S†} {S = S} {R = R} {A = A} A∈ α∈)
      ; c → {!!}
      }


-- T0D0 induction on list of honest strategies
-- T0D0 induction on the run itself
-}
