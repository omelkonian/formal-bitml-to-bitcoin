open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Accessors

module SymbolicModel.Accessors
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Run Participant Honest

unquoteDecl _∙Cfg _∙cfg ∙cfg=_ = genAccessor _∙Cfg _∙cfg ∙cfg=_ (quote Cfg)
instance
  Cfgᵗ∙Cfg : Cfgᵗ ∙Cfg
  Cfgᵗ∙Cfg = ∙cfg= cfg

  Run∙Cfg : Run ∙Cfg
  Run∙Cfg = ∙cfg= (_∙cfg ∘ end)

-- unquoteDecl _∙Run _∙run ∙run=_ = genAccessor _∙Run _∙run ∙run=_ (quote Run)
-- instance
--    ∃ℝ-has-Run : (∃ ℝ) ∙Run
--    ∃ℝ-has-Run = ∙run= proj₁

--    ℝˢ-has-Run : ℝˢ Rˢ ∙Run
--    ℝˢ-has-Run = ∙run= λ where (_⦊_ R {Γ} (𝕒 , _)) → Γ ∷ R ⊣ 𝕒

--    ℝˢ-has-ℝ : HasField′ ℝˢ (ℝ ∘ _∙run)
--    ℝˢ-has-ℝ ._∙ (_ ⦊ _ , 𝕣) = 𝕣
