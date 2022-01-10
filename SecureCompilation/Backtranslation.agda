{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership

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
open import ComputationalModel Participant Honest finPart keypairs as C
open import SecureCompilation.Coherence Participant Honest finPart keypairs η as SC

module _ (A∈ : A ∈ S.Hon) (Rᶜ : C.Run) where
  Rᶜ∗ = strip A Rᶜ

  parseRun : C.Run → S.Run
  parseRun [] = {!!} -- T0D0: assume Rᶜ is non-empty?
  parseRun (l ∷ ls) =
    let
      Rˢ = parseRun ls
    in
      case l of λ where
        (x →∗∶ x₁) → {!!}
        (submit x) → {!!}
        (delay δ) → {!!}
        (x →O∶ x₁) → {!!}
        (O→ x ∶ x₁) → {!!}

  ℵ : S.ParticipantStrategy A → C.ParticipantStrategy A
  ℵ Σˢ = Σᶜ
    where
      go : C.Run → C.Labels
      go Rᶜ =
        let
          Rᶜ∗ : C.Run
          Rᶜ∗ = Rᶜ -- ∗

          -- (1) parse the (stripped) run Rᶜ∗, so to obtain a corresponding sumbolic (stripped) run Rˢ∗
          Rˢ∗ : S.Run
          Rˢ∗ = parseRun Rᶜ∗

          -- (3) evaluate Λˢ = Σˢ(Rˢ∗)
          Λˢ : S.Labels
          Λˢ = Σˢ .S.Σ Rˢ∗

          -- (4) convert the symbolic actions Λˢ into computational actions Λᶜ
          -- when Λˢ contains A:{G}C,Δ or A:{G}C,x follow stipulation protocol
          Λᶜ : C.Labels
          Λᶜ = flip map Λˢ $ λ where
            auth-join⦅ x , x₁ ↔ x₂ ⦆ → {!!}
            join⦅ x ↔ x₁ ⦆ → {!!}
            auth-divide⦅ x , x₁ ▷ x₂ , x₃ ⦆ → {!!}
            divide⦅ x ▷ x₁ , x₂ ⦆ → {!!}
            auth-donate⦅ x , x₁ ▷ᵈ x₂ ⦆ → {!!}
            donate⦅ x ▷ᵈ x₁ ⦆ → {!!}
            auth-destroy⦅ x , xs , x₁ ⦆ → {!!}
            destroy⦅ x ⦆ → {!!}
            advertise⦅ x ⦆ → {!!}
            auth-commit⦅ x , x₁ , x₂ ⦆ → {!!}
            auth-init⦅ x , x₁ , x₂ ⦆ → {!!}
            init⦅ x , x₁ ⦆ → {!!}
            split⦅ x ⦆ → {!!}
            auth-rev⦅ x , x₁ ⦆ → {!!}
            put⦅ x , x₁ , x₂ ⦆ → {!!}
            withdraw⦅ x , x₁ , x₂ ⦆ → {!!}
            auth-control⦅ x , x₁ ▷ x₂ ⦆ → {!!}
            delay⦅ x ⦆ → {!!}
        in
          Λᶜ

      Σᶜ : C.ParticipantStrategy A
      Σᶜ = record {Σ = go}
