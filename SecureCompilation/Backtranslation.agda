---------------------------------------------------------
-- Translating symbolic strategies to computational ones.
---------------------------------------------------------

open import Prelude.Init hiding (T)
open L.Mem using (_∈_; ∈-map⁻; mapWith∈)
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership hiding (_∈_; mapWith∈)
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

open import Bitcoin using (KeyPair)
open import SecureCompilation.ModuleParameters using (⋯)

module SecureCompilation.Backtranslation (⋯ : ⋯) (let open ⋯ : ⋯) where

open import SymbolicModel ⋯′ as S
  hiding (Rˢ′; d)
open import SymbolicModel.Stripping ⋯′
open import ComputationalModel ⋯′ finPart keypairs as C
  hiding (Initial; Σ; t; t′; `; ∣_∣; n)
open import SecureCompilation.Helpers ⋯
open import SecureCompilation.Coherence ⋯ as SC
open import SecureCompilation.Backtranslation.Parsing ⋯
  using (parseRun)

module _ {A} (A∈ : A ∈ S.Hon) where

  open import SecureCompilation.Backtranslation.Unparsing ⋯ A
    using (unparseMoves)

  ℵ : 𝕍 (S.ParticipantStrategy A) → 𝕍 (C.ParticipantStrategy A)
  ℵ (Σˢ , 𝕧ˢ@(_ , rule-abiding , _)) = Σᶜ , 𝕧ᶜ
    where
      go : CRun → C.Labels
      go Rᶜ =
        let
          Rᶜ∗ : CRun
          Rᶜ∗ = Rᶜ -- ∗

          -- (1) parse the (stripped) run Rᶜ∗, so to obtain a corresponding
          -- symbolic (stripped) run Rˢ∗
          Rˢ , Rˢ~Rᶜ = parseRun Rᶜ∗
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
