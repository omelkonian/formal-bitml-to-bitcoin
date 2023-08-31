---------------------------------------------------------
-- Translating symbolic strategies to computational ones.
---------------------------------------------------------
open import Prelude.Init
open import Prelude.Membership
open import Prelude.Validity

open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.StrategyTranslation (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
open import SymbolicModel.Stripping ⋯′
open import ComputationalModel ⋯′ finPart keypairs as C
open import Coherence ⋯
open import SecureCompilation.Parsing ⋯
  using (parseRun~)

postulate instance _ : Strippable CRun

module _ {A} (A∈ : A ∈ Hon) where

  open import SecureCompilation.Unparsing ⋯ A
    using (unparseMoves)

  ℵ : 𝕍 (S.ParticipantStrategy A) → 𝕍 (C.ParticipantStrategy A)
  ℵ (Σˢ , 𝕧ˢ@(_ , rule-abiding , _)) = Σᶜ , 𝕧ᶜ
    where
      go : CRun → C.Labels
      go Rᶜ =
        let
          Rᶜ∗ = Rᶜ ∗

          -- (1) parse run Rᶜ∗ to obtain a corresponding symbolic run Rˢ∗
          Rˢ , Rˢ~Rᶜ = parseRun~ Rᶜ∗
          Rˢ∗ = Rˢ ∗

          -- (3) evaluate Λˢ = Σˢ(Rˢ∗)
          Λˢ : S.Labels
          Λˢ = Σˢ .S.Σ Rˢ∗

          Λˢ′ : List (∃ λ α → ∃ (Rˢ ——[ α ]→_))
          Λˢ′ = mapWith∈ Λˢ (-,_ ∘ rule-abiding {R = Rˢ})

          -- (4) convert the symbolic actions Λˢ into computational actions Λᶜ
          -- when Λˢ contains A:{G}C,Δ or A:{G}C,x follow stipulation protocol
          Λᶜ : C.Labels
          Λᶜ = unparseMoves Rˢ~Rᶜ Λˢ′
        in
          Λᶜ

      Σᶜ : C.ParticipantStrategy A
      Σᶜ = record {Σ = go}

      postulate 𝕧ᶜ : Valid Σᶜ
