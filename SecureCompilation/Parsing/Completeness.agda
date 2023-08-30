-------------------------------------------------
-- Parsing computational runs into symbolic ones.
-------------------------------------------------
open import Prelude.Init
open import Prelude.Lists.Mappings
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Functor
open import Prelude.Apartness
open import Prelude.Ord

open import Bitcoin using (KeyPair)
open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Parsing.Completeness (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
  hiding (Rˢ′; d; Γₜ″)
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Σ; t; t′; `; ∣_∣; n)

open import Coherence ⋯ as SC
open import SecureCompilation.Parsing.Dec ⋯

parseRun : (Rᶜ : CRun) → ∃ (_~ Rᶜ)
parseRun (Rᶜ ∎⊣ init ✓) = ∅ˢ , ℝ∗-∅ˢ , base auto init (λ ())
parseRun (λᶜ ∷ Rᶜ ✓)
  with Rˢ , 𝕣∗ , Rˢ~Rᶜ ← parseRun Rᶜ
  with λᶜ
parseRun _ | A →O∶  m =
  Rˢ , 𝕣∗ , step₂ Rˢ~Rᶜ ([2] $′ inj₁ refl)
parseRun _ | O→ A ∶ m =
  Rˢ , 𝕣∗ , step₂ Rˢ~Rᶜ ([2] $′ inj₂ refl)
parseRun _ | delay 0 =
  Rˢ , 𝕣∗ , step₂ Rˢ~Rᶜ [2]′
parseRun (_ ∷ Rᶜ ✓) | delay (suc _) =
  -, -, step₁ Rˢ~Rᶜ ([L18] mkℍ {h})
  where
    h : H₁₈-args
    h = mk {Γ = Rˢ ∙cfg} auto (Rᶜ ⨾ Rˢ ⨾ 𝕣∗ ⊣ refl , ↭-refl ≈ Rˢ ∙cfg ⊣ ↭-refl)
parseRun (_ ∷ Rᶜ ✓) | A₀ →∗∶ m₀
  with dec-H₁ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓1)
  = -, -, step₁ Rˢ~Rᶜ ([L1] ✓1)
... | no ¬1
  with dec-H₂ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓2)
  = -, -, step₁ Rˢ~Rᶜ ([L2] ✓2)
... | no ¬2
  with dec-H₃ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓3)
  = -, -, step₁ Rˢ~Rᶜ ([L3] ✓3)
... | no ¬3
  with dec-H₅ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓5)
  = -, -, step₁ Rˢ~Rᶜ ([L5] ✓5)
... | no ¬5
  with dec-H₇ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓7)
  = -, -, step₁ Rˢ~Rᶜ ([L7] ✓7)
... | no ¬7
  with dec-H₁₀ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓10)
  = -, -, step₁ Rˢ~Rᶜ ([L10] ✓10)
... | no ¬10
  with dec-H₁₂ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓12)
  = -, -, step₁ Rˢ~Rᶜ ([L12] ✓12)
... | no ¬12
    with dec-H₁₄ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓14)
  = -, -, step₁ Rˢ~Rᶜ ([L14] ✓14)
... | no ¬14
  with dec-H₁₆ Rˢ 𝕣∗ Rᶜ A₀ m₀
... | yes (_ , _ , ✓16)
  = -, -, step₁ Rˢ~Rᶜ
    ([R16⊣ ¬H[1-14] Rˢ 𝕣∗ Rᶜ A₀ m₀ ¬1 ¬2 ¬3 ¬5 ¬7 ¬10 ¬12 ¬14 _ _ ] ✓16)
... | no ¬16
  = -, -, step₂ Rˢ~Rᶜ ([3] $ ¬H16⇒≁₁ Rˢ 𝕣∗ Rᶜ A₀ m₀ ¬16)
parseRun (_ ∷ Rᶜ ✓) | submit T₀
  with dec-H₄ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓4)
  = -, -, step₁ Rˢ~Rᶜ ([L4] ✓4)
... | no ¬4
  with dec-H₆ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓6)
  = -, -, step₁ Rˢ~Rᶜ ([L6] ✓6)
... | no ¬6
  with dec-H₈ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓8)
  = -, -, step₁ Rˢ~Rᶜ ([L8] ✓8)
... | no ¬8
  with dec-H₉ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓9)
  = -, -, step₁ Rˢ~Rᶜ ([L9] ✓9)
... | no ¬9
  with dec-H₁₁ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓11)
  = -, -, step₁ Rˢ~Rᶜ ([L11] ✓11)
... | no ¬11
  with dec-H₁₃ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓13)
  = -, -, step₁ Rˢ~Rᶜ ([L13] ✓13)
... | no ¬13
  with dec-H₁₅ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓15)
  = -, -, step₁ Rˢ~Rᶜ ([L15] ✓15)
... | no ¬15
  with dec-H₁₇ Rˢ 𝕣∗ Rᶜ T₀
... | yes (_ , _ , ✓17)
  = -, -, step₁ Rˢ~Rᶜ
    ([R17⊣ ¬H[4-15] Rˢ 𝕣∗ Rᶜ T₀ ¬4 ¬6 ¬8 ¬9 ¬11 ¬13 ¬15 _ _ ] ✓17)
... | no ¬17
  = -, 𝕣∗ , step₂ Rˢ~Rᶜ ([1] ins♯)
  where
    open ℝ (ℝ∗⇒ℝ 𝕣∗)
    ins♯ : ∃inputs T₀ ♯ (hashTxⁱ <$> codom txout′)
    ins♯ = ¬H17⇒♯ Rˢ 𝕣∗ Rᶜ T₀ ¬17
