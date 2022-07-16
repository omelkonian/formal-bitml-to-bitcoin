-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership
open import Prelude.Ord

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
        (A →∗∶ m)  → {!!}
        (submit T) → {!!}
        (delay 0)  → Rˢ
        (delay δ@(suc _))  →
          let Γₜ@(Γ at t) = Rˢ .end
              Γₜ′ = Γ at (t + δ)
          in Γₜ′ ∷ Rˢ
          ⊣ (delay⦅ δ ⦆ , Γₜ , Γₜ′ , [Delay] (s≤s z≤n) , (refl , ↭-refl) , (refl , ↭-refl))
        (A →O∶ m)  → {!!}
        (O→ A ∶ m) → {!!}

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
