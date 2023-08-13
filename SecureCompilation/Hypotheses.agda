-----------------------------------------------
-- Hypotheses for each coherence rule.
-----------------------------------------------

open import Prelude.Init hiding (T)
open L.Mem
open import Prelude.Lists
open import Prelude.General
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.InferenceRules

open import Prelude.Lists.Collections
open import Prelude.Monoid

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Ord
open import Prelude.ToN
open import Prelude.ToList
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.Split hiding (split)
open import Prelude.Serializable
open import Prelude.Views hiding (_▷_)
open import Prelude.Null

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Hypotheses (⋯ : ⋯) (let open ⋯ : ⋯) where

open import SymbolicModel ⋯′ as S
  hiding (_∎; begin_; d; Γₜ″)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Σ ; t; t′; `; ∣_∣; n)

open import SecureCompilation.ComputationalContracts ⋯′
open import Compiler ⋯′ η
open import SecureCompilation.Helpers ⋯

module _ (Rˢ : S.Run) (𝕣∗ : ℝ∗ Rˢ) (Rᶜ : CRun) where
  𝕣 = ℝ∗⇒ℝ 𝕣∗
  open ℝ 𝕣
  module _ (A₀ : Participant) (m₀ : Message) where
    module _ (⟨G⟩C : Ad) where
      ℍ[1] : Set
      ℍ[1] = let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G; Γ = Rˢ ∙cfg in
        ∃ λ (vad : Valid ⟨G⟩C)
        → Any (_∈ S.Hon) partG
        × ∃ λ (d⊆ : ⟨G⟩C ⊆⦅ deposits ⦆ Γ) →
        let
          txoutΓ = Txout Γ ∋ 𝕣 ∙txoutEnd_
          txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
          txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad .names-⊆)
          C = encodeAd ⟨G⟩C (txoutG , txoutC)
        in
         m₀ ≡ C

-- ℍ[1] :
--       let
--         Γₜ = Γ at t
--       in
--       (R≈ : Rˢ ≈⋯ Γₜ)
--     → let
--         α   = advertise⦅ ⟨G⟩C ⦆
--         Γ′  = ` ⟨G⟩C ∣ Γ
--         t′  = t
--         Γₜ′ = Γ′ at t′
--       in
--       (∃Γ≈ : ∃ (_≈ᶜ Γ′)) → let Γₜ″ = ∃Γ≈ .proj₁ at t′ in
--       -- Hypotheses from [C-Advertise]
--       (vad : Valid ⟨G⟩C)
--       (hon : Any (_∈ Hon) partG)
--       (d⊆  : ⟨G⟩C ⊆⦅ deposits ⦆ Γ)
--     → let
--         Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
--         Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

--         -- txout′ = txout, sechash′ = sechash, κ′ = κ
--         open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈ using (λˢ)

--         C =
--           let
--             txoutΓ = Txout Γ ∋ Txout≈ {Rˢ ∙cfg}{Γ} (R≈ .proj₂) (𝕣 ∙txoutEnd_)
--             txoutG = Txout G ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{Γ} d⊆)
--             txoutC = Txout C ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad .names-⊆)
--           in
--             encodeAd ⟨G⟩C (txoutG , txoutC)
--         λᶜ = A →∗∶ C
--       in
--       ────────────────────────────────────────────────────
--       (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓)
