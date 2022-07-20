-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Validity

open import Bitcoin

module SecureCompilation.Backtranslation
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (Rˢ′)
open import ComputationalModel Participant Honest finPart keypairs as C
open import SecureCompilation.Coherence Participant Honest finPart keypairs η as SC

postulate
  decode : Txout Rˢ → Message → Maybe Ad
  -- ^ decode bitstring as {G}C, converting outputs `txout(x)` to names `x`

module _ (A∈ : A ∈ S.Hon) (Rᶜ : C.Run) where
  Rᶜ∗ = strip A Rᶜ

  ∅ˢ : S.Run
  ∅ˢ = (∅ᶜ at 0) ∎⊣ (tt , refl)

  𝕣∅ˢ : ∃ ℝ
  𝕣∅ˢ = ∅ˢ , record {txout = λ (); sechash = λ (); κ = λ ()}

  -- parseRun : (Rᶜ : C.Run) → ∃ (_~ Rᶜ)
  parseRun : C.Run → S.Run
  parseRun = proj₁      -- extract the resulting symbolic run
           ∘ go 𝕣∅ˢ []  -- exploit mappings txout/sechash/κ to perform parsing
           ∘ ignoreDups -- ignore duplicate messages
    where
      ignoreDups : Op₁ C.Run
      ignoreDups = L.reverse ∘ nub ∘ L.reverse

      go : ∃ ℝ          -- (well-formed) symbolic run constructed so far
         → List C.Label -- computational labels that have been already processed
         → C.Run        -- computational labels to process
         → ∃ ℝ          -- resulting (well-formed) symbolic run
      go ∃𝕣 _ [] = ∃𝕣 -- finished processing Rᶜ, return
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ)
        with λᶜ
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | delay δ
        with δ >? 0
      ... | yes δ>0
        -- [18]
        = go ( (_ ∷ Rˢ ⊣≡ (delay⦅ δ ⦆ , [Delay] δ>0))
             , record {txout = {!!}; sechash = {!!}; κ = {!!}} )
             (λᶜ ∷ prev-Rᶜ) Rᶜ
      ... | no  δ≯0
        -- invalid [18]; ignore
        = go ∃𝕣 prev-Rᶜ Rᶜ
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | A →∗∶ m
        with decode {Rˢ} (𝕣 .𝕎.txout) m
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | A →∗∶ m | just ⟨G⟩C@(⟨ G ⟩ C)
        with ¿ Valid ⟨G⟩C ¿ | any? (_∈? S.Hon) (nub-participants G) | deposits ⟨G⟩C ⊆? deposits (Rˢ ∙cfg)
      ... | yes vad | yes hon | yes d⊆
        -- [1]
        = go ( (_ ∷ Rˢ ⊣≡ (advertise⦅ ⟨G⟩C ⦆ , [Action] ([C-Advertise] vad hon d⊆) refl))
             , record {txout = {!!}; sechash = {!!}; κ = {!!}} )
             (λᶜ ∷ prev-Rᶜ) Rᶜ
      ... | _ | _ | _
        -- invalid [1]; ignore
        = go ∃𝕣 prev-Rᶜ Rᶜ
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | A →∗∶ m | nothing
        = {!!}

      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | submit T = {!!}
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | A →O∶ m  = {!!}
      go ∃𝕣@(Rˢ , 𝕣) prev-Rᶜ (λᶜ ∷ Rᶜ) | O→ A ∶ m = {!!}

  -- parseRun [] = {!!} -- T0D0: assume Rᶜ is non-empty?
  -- parseRun (l ∷ ls) =
  --   let
  --     Rˢ = parseRun ls
  --   in
  --     case l of λ where
  --       (A →∗∶ m)  → {!!}
  --       (submit T) → {!!}
  --       (delay 0)  → Rˢ
  --       (delay δ@(suc _))  →
  --         let Γₜ@(Γ at t) = Rˢ .end
  --             Γₜ′ = Γ at (t + δ)
  --         in Γₜ′ ∷ Rˢ
  --         ⊣ (delay⦅ δ ⦆ , Γₜ , Γₜ′ , [Delay] (s≤s z≤n) , (refl , ↭-refl) , (refl , ↭-refl))
  --       (A →O∶ m)  → {!!}
  --       (O→ A ∶ m) → {!!}

  ℵ : S.ParticipantStrategy A → C.ParticipantStrategy A
  ℵ Σˢ = Σᶜ
    where
      go : C.Run → C.Labels
      go Rᶜ =
        let
          Rᶜ∗ : C.Run
          Rᶜ∗ = Rᶜ -- ∗

          -- (1) parse the (stripped) run Rᶜ∗, so to obtain a corresponding
          -- symbolic (stripped) run Rˢ∗
          Rˢ∗ : S.Run
          Rˢ∗ = parseRun Rᶜ∗

          -- (3) evaluate Λˢ = Σˢ(Rˢ∗)
          Λˢ : S.Labels
          Λˢ = Σˢ .S.Σ Rˢ∗

          -- (4) convert the symbolic actions Λˢ into computational actions Λᶜ
          -- when Λˢ contains A:{G}C,Δ or A:{G}C,x follow stipulation protocol
          Λᶜ : C.Labels
          Λᶜ = flip map Λˢ $ λ where
            auth-join⦅ A , x ↔ y ⦆        → {!!}
            join⦅ x ↔ y ⦆                 → {!!}
            auth-divide⦅ A , x ▷ v , v′ ⦆ → {!!}
            divide⦅ A ▷ v , v′ ⦆          → {!!}
            auth-donate⦅ A , x ▷ᵈ B ⦆     → {!!}
            donate⦅ x ▷ᵈ B ⦆              → {!!}
            auth-destroy⦅ A , xs , j ⦆    → {!!}
            destroy⦅ xs ⦆                 → {!!}
            advertise⦅ ad ⦆               → {!!}
            auth-commit⦅ A , ad , Δ ⦆     → {!!}
            auth-init⦅ A , ad , x ⦆       → {!!}
            init⦅ G , C ⦆                 → {!!}
            split⦅ y ⦆                    → {!!}
            auth-rev⦅ A , a ⦆             → {!!}
            put⦅ xs , as , y ⦆            → {!!}
            withdraw⦅ A , v , y ⦆         → {!!}
            auth-control⦅ A , x ▷ D ⦆     → {!!}
            delay⦅ δ ⦆                    → {!!}
        in
          Λᶜ

      Σᶜ : C.ParticipantStrategy A
      Σᶜ = record {Σ = go}
