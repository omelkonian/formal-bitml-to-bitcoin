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
open import Prelude.Setoid
open import Prelude.InferenceRules

open import Bitcoin using (KeyPair)

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
  hiding (Hon; Initial; Σ
         ; t; t′; `; ∣_∣; n)

open import SecureCompilation.Helpers  Participant Honest finPart keypairs η
open import SecureCompilation.Coherence Participant Honest finPart keypairs η as SC

postulate
  decode : Txout Rˢ → Message → Maybe Ad
  -- ^ decode bitstring as {G}C, converting outputs `txout(x)` to names `x`

  encode-decode : ∀ {Rˢ} (𝕣 : ℝ Rˢ) m → let open ℝ 𝕣 in
    ∀ ad →
      decode {Rˢ} txout′ m ≡ just ad
      ══════════════════════════════
      m ≡ encode {Rˢ} txout′ ad

try-decode : ∀ {Rˢ} (𝕣∗ : ℝ∗ Rˢ) m → let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣 in
    (∃ λ ad → m ≡ encode {Rˢ} txout′ ad)
  ⊎ (∀ ad → m ≢ encode {Rˢ} txout′ ad)
try-decode {Rˢ} 𝕣∗ m
  with 𝕣 ← ℝ∗⇒ℝ 𝕣∗
  with decode {Rˢ} (𝕣 .ℝ.txout′) m | encode-decode {Rˢ = Rˢ} 𝕣 m
... | just ad | p = inj₁ (ad , p ad .proj₁ refl)
... | nothing | p = inj₂ λ ad → λ where refl → case p ad .proj₂ refl of λ ()

{-

[1]: A →∗: C
 where
  ∙ C = encode {Rˢ} txout′ ⟨G⟩C
  ∙ Valid ⟨G⟩C
  ∙ Any (_∈ Hon) partG
  ∙ ⟨G⟩C ⊆⦅ deposits ⦆ Γ

[2]: B →∗∶ SIGᵐ (K A) C,h̅,k̅
 where
  ∙ C = encode {Rˢ} txout′ ⟨G⟩C
  ∙ h̅ = map (proj₂ ∘ proj₂) Δ×h̅
  ∙ k̅ = concatMap (map pub ∘ codom) (codom k⃗)
  ∘ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C}

[3]: B →∗∶ SIG (K̂ A) Tᵢₙᵢₜ

[4]: submit Tᵢₙᵢₜ

[5]: B →∗∶ SIGᵖ pubK T -- auth.control

[6]: submit T -- put

[7]: B →∗∶ ??? -- auth.reveal

[8]: submit T -- split

[9]: submit T -- withdraw

[10]: B →∗∶ SIG (K̂ A) T -- auth.join

[11]: submit T -- join

[12]: B →∗∶ SIG (K̂ A) T -- auth.divide

[13]: submit T -- divide

[14]: B →∗∶ SIG (K̂ A) T -- auth.donate

[15]: submit T -- donate

[16]: B →∗∶ SIG (K̂ A) T -- auth.destroy

[17]: submit T -- destroy

[18]: delay⦅ δ ⦆

-}

ℾ-∅ : ℾ ∅ᶜ
ℾ-∅ = record {txout = λ (); sechash = λ (); κ = λ ()}

∅ᵗ : Cfgᵗ
∅ᵗ = ∅ᶜ at 0

ℾᵗ-∅ᵗ : ℾᵗ ∅ᵗ
ℾᵗ-∅ᵗ = record {txout = λ (); sechash = λ (); κ = λ ()}

ℝ∗-∅ˢ : ℝ∗ ∅ˢ
ℝ∗-∅ˢ = ℾᵗ-∅ᵗ ∎⊣ auto ✓

parseRun : (Rᶜ : CRun) → ∃ (_~ Rᶜ)
parseRun (Rᶜ ∎⊣ init ✓) = ∅ˢ , ℝ∗-∅ˢ , base auto init (λ ())
parseRun ((A →O∶  m) ∷ Rᶜ ✓) =
  let Rˢ , 𝕣 , Rˢ~Rᶜ = parseRun Rᶜ
  in  Rˢ , 𝕣 , step₂ Rˢ~Rᶜ ([2] $′ inj₁ refl)
parseRun ((O→ A ∶ m) ∷ Rᶜ ✓) =
  let Rˢ , 𝕣 , Rˢ~Rᶜ = parseRun Rᶜ
  in  Rˢ , 𝕣 , step₂ Rˢ~Rᶜ ([2] $′ inj₂ refl)
parseRun (delay δ ∷ Rᶜ ✓)
  with δ >? 0
... | yes δ>0
  -- [18]
  = let
      Rˢ , 𝕣∗ , Rˢ~Rᶜ = parseRun Rᶜ
      𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

      Γₜ@(Γ at t) = Rˢ .end
      α   = delay⦅ δ ⦆
      t′  = t + δ
      Γₜ′ = Γ at t′
      -- λᶜ  = delay δ

      ∃Γ≈ : ∃ (_≈ᶜ Γ)
      ∃Γ≈ = Γ , ↭-refl

      Γₜ″ = ∃Γ≈ .proj₁ at t′

      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Delay] δ>0

      open H₁₈ {Rˢ} 𝕣 t α t′ Γ (≈ᵗ-refl {Γₜ}) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
      -, (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) , step₁ Rˢ~Rᶜ ([L] [18] δ>0 ∃Γ≈)
... | no  δ≯0
  -- invalid [18]; ignore
  -- cannot use [R] [3] as it only covers `A →∗∶ m` messages, not delays
  = {!!}
parseRun ((A →∗∶ m) ∷ Rᶜ ✓)
  with Rˢ , 𝕣∗ , Rˢ~Rᶜ ← parseRun Rᶜ
  with try-decode {Rˢ = Rˢ} 𝕣∗ m
... | inj₂ m≢
  -- invalid [1]; ignore
  = {!!}
... | inj₁ (⟨G⟩C , refl)
  -- Hypotheses from [C-Advertise]
  with ¿ Valid ⟨G⟩C ¿
 ×-dec any? (_∈? S.Hon) (nub-participants (⟨G⟩C .G))
 ×-dec deposits ⟨G⟩C ⊆? deposits (Rˢ ∙cfg)
... | yes (vad , hon , d⊆)
  -- [1]
  = let
      -- Rˢ , 𝕣∗ , Rˢ~Rᶜ = parseRun Rᶜ
      𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

      Γₜ@(Γ at t) = Rˢ .end

      ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G
      Γₜ = Γ at t

      R≈ : Rˢ ≈⋯ Γₜ
      R≈ = refl , ↭-refl

      α   = advertise⦅ ⟨G⟩C ⦆
      Γ′  = ` ⟨G⟩C ∣ Γ
      t′  = t
      Γₜ′ = Γ′ at t′

      -- C  = encode {Rˢ} txout′ ⟨G⟩C
      -- λᶜ = A →∗∶ C

      ∃Γ≈ : ∃ (_≈ᶜ Γ′)
      ∃Γ≈ = Γ′ , ↭-refl

      Γₜ″ = ∃Γ≈ .proj₁ at t′

      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

      -- txout′ = txout, sechash′ = sechash, κ′ = κ
      open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈ using (λˢ)
    in
      -, (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) , step₁ Rˢ~Rᶜ ([L] [1] R≈ ∃Γ≈ vad hon d⊆)
... | no ¬vad×hon×d⊆
  -- invalid [1]; ignore
  = {!!}
parseRun (submit T ∷ Rᶜ ✓)
  = {!!}

--   ℵ : S.ParticipantStrategy A → C.ParticipantStrategy A
--   ℵ Σˢ = Σᶜ
--     where
--       go : C.Run → C.Labels
--       go Rᶜ =
--         let
--           Rᶜ∗ : C.Run
--           Rᶜ∗ = Rᶜ -- ∗

--           -- (1) parse the (stripped) run Rᶜ∗, so to obtain a corresponding
--           -- symbolic (stripped) run Rˢ∗
--           Rˢ∗ : S.Run
--           Rˢ∗ = parseRun Rᶜ∗

--           -- (3) evaluate Λˢ = Σˢ(Rˢ∗)
--           Λˢ : S.Labels
--           Λˢ = Σˢ .S.Σ Rˢ∗

--           -- (4) convert the symbolic actions Λˢ into computational actions Λᶜ
--           -- when Λˢ contains A:{G}C,Δ or A:{G}C,x follow stipulation protocol
--           Λᶜ : C.Labels
--           Λᶜ = flip map Λˢ $ λ where
--             auth-join⦅ A , x ↔ y ⦆        → {!!}
--             join⦅ x ↔ y ⦆                 → {!!}
--             auth-divide⦅ A , x ▷ v , v′ ⦆ → {!!}
--             divide⦅ A ▷ v , v′ ⦆          → {!!}
--             auth-donate⦅ A , x ▷ᵈ B ⦆     → {!!}
--             donate⦅ x ▷ᵈ B ⦆              → {!!}
--             auth-destroy⦅ A , xs , j ⦆    → {!!}
--             destroy⦅ xs ⦆                 → {!!}
--             advertise⦅ ad ⦆               → {!!}
--             auth-commit⦅ A , ad , Δ ⦆     → {!!}
--             auth-init⦅ A , ad , x ⦆       → {!!}
--             init⦅ G , C ⦆                 → {!!}
--             split⦅ y ⦆                    → {!!}
--             auth-rev⦅ A , a ⦆             → {!!}
--             put⦅ xs , as , y ⦆            → {!!}
--             withdraw⦅ A , v , y ⦆         → {!!}
--             auth-control⦅ A , x ▷ D ⦆     → {!!}
--             delay⦅ δ ⦆                    → {!!}
--         in
--           Λᶜ

--       Σᶜ : C.ParticipantStrategy A
--       Σᶜ = record {Σ = go}
