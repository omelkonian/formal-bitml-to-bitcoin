open import Prelude.Init
open import Prelude.Lists
open L.Mem using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Bifunctor
open import Prelude.Nary

open import Bitcoin.Crypto using (KeyPair)
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto

module SymbolicModel.Derived
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Strategy Participant Honest
open import SymbolicModel.Helpers Participant Honest

private variable ⟨G⟩C : Advertisement

h : let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in

    (R : Run)
  → Valid R
  → (cfg≡ : R ≡⋯ (` ⟨G⟩C ∣ Γ at t))
    --———————————————————————————————————————————
   → ∃ λ Γ₀ → (` ⟨G⟩C ∉ᶜ Γ₀) × (Γ₀ —[ αs ]↠ ` ⟨G⟩C ∣ Γ)
h {⟨G⟩C}{Γ}{t} ((.((` ⟨G⟩C ∣ Γ) at t) ∙)) () refl
h {⟨G⟩C}{Γ}{t} (.((` ⟨G⟩C ∣ Γ) at t) ∷⟦ α ⟧ R) vR refl = {!!}

adv : let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in

    (R : Run)
  → Valid R
  → (cfg≡ : R ≡⋯ (` ⟨G⟩C ∣ Γ at t))
    --——————————————————————
   → ValidAdvertisement ⟨G⟩C
adv {⟨G⟩C}{Γ}{t} ((.((` ⟨G⟩C ∣ Γ) at t) ∙)) () refl
adv {⟨G⟩C}{Γ}{t} (.((` ⟨G⟩C ∣ Γ) at t) ∷⟦ α ⟧ R) vR refl = {!!}


-- adv : let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in

--     (R : Run)
--   → Valid R
--   → (cfg≡ : R ≡⋯ (` ⟨G⟩C ∣ Γ at t))
--     --————————————————————————————————————————————————————————————
--    → advertise⦅ ⟨G⟩C ⦆ ∈ labels R
-- adv {⟨G⟩C}{Γ}{t} ((.((` ⟨G⟩C ∣ Γ) at t) ∙)) vR refl = case vR of λ ()
-- adv {⟨G⟩C}{Γ}{t} (.((` ⟨G⟩C ∣ Γ) at t) ∷⟦ α ⟧ R) vR refl = {!!}


--   -- [C-AuthInit] : let ⟨ G ⟩ _ = ad; partG = nub-participants G in

--   --     partG ⊆ committedParticipants Γ ad -- all participants have committed their secrets
--   --   → (A , v , x) ∈ persistentDeposits G -- G = A :! v @ x | ...
--   --     --——————————————————————————————————————————————————————————————————————
--   --   → ` ad ∣ Γ
--   --       —→[ auth-init[ A , ad , x ] ]
--   --     ` ad ∣ Γ ∣ A auth[ x ▷ˢ ad ]



--   -- [3] : ∀ {⟨G⟩C} {vad : ValidAdvertisement ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G in
--   --       ∀ {t A Γ₀} → let Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in

--   --     (cfg≡ : Rˢ ≡⋯ Γₜ)

--   --   → let
--   --       α   = auth-init[ A , ⟨G⟩C , x ]
--   --       Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
--   --       t′  = t
--   --       Γₜ′ = Γ′ at t′
--   --     in

-- h : let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in

--     (R : Run)
--   → Valid R
--   → (cfg≡ : R ≡⋯ (` ⟨G⟩C ∣ Γ at t))
--     -- Hypotheses from [C-AuthInit]
--   → (committedA : partG ⊆ committedParticipants Γ ⟨G⟩C)
--     --————————————————————————————————————————————————————————————
--     --   ∙ from the hypotheses of [C-Advertise]
--     --       ∘ which introduces ` ⟨G⟩C
--     --       ⇒ deposits ⟨G⟩C ⊆ deposits Γ₀
--     --       ⇒ namesʳ ⟨G⟩C ⊆ namesʳ Γ₀
--     --   ∙ from the hypotheses of [C-AuthCommit]
--     --       ∘ which introduces ⟨ Aᵢ ∶ aᵢ ♯ Nᵢ ⟩
--      --       ⇒ secrets ⟨G⟩C ⊆ secrets Γ₀
--     --       ⇒ namesˡ ⟨G⟩C ⊆ namesˡ Γ₀
--    → G ⊆⟨on:names⟩ Γ
-- h = {!!}

-- hˡ : let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in

--     (R : Run)
--   → Valid R
--   → (cfg≡ : R ≡⋯ ` ⟨G⟩C ∣ Γ at t)
--     -- Hypotheses from [C-AuthInit]
--   → (committedA : partG ⊆ committedParticipants Γ ⟨G⟩C)
--     --————————————————————————————————————————————————————————————
--     -- ∙ from the hypotheses of [C-AuthCommit]
--     --   ∘ which introduces ⟨ Aᵢ ∶ aᵢ ♯ Nᵢ ⟩
--     --     ⇒ secrets ⟨G⟩C ⊆ secrets Γ₀
--     --     ⇒ namesˡ ⟨G⟩C ⊆ namesˡ Γ₀
--    → namesˡ G ⊆ namesˡ Γ
-- hˡ = {!!}

-- hʳ : let ⟨ G ⟩ C = ⟨G⟩C; partG = nub-participants G in

--     (R : Run)
--   → Valid R
--   → (cfg≡ : R ≡⋯ ` ⟨G⟩C ∣ Γ at t)
--     -- Hypotheses from [C-AuthInit]
--   → (committedA : partG ⊆ committedParticipants Γ ⟨G⟩C)
--     --————————————————————————————————————————————————————————————
--     -- ∙ from the hypotheses of [C-Advertise]
--     --   ∘ which introduces ` ⟨G⟩C
--     --     ⇒ deposits ⟨G⟩C ⊆ deposits Γ₀
--     --     ⇒ namesʳ ⟨G⟩C ⊆ namesʳ Γ₀
--    → namesʳ G ⊆ namesʳ Γ
-- hʳ {⟨G⟩C = ⟨G⟩C@(⟨ G ⟩ C )} {Γ = Γ} R 𝕍R cfg≡ comA = qed
--   where
--     qed : namesʳ G ⊆ namesʳ Γ
--     qed = {!!}
