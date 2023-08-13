open import Prelude.Init; open SetAsType
open import Prelude.Lists.Mappings

open import BitML.BasicTypes using (⋯)

module Compiler.Subterms (⋯ : ⋯) where

open import BitML ⋯
  hiding (begin_; _∎)
open import Compiler.Outputs ⋯

map-↦ : ∀ {A B : Type} {C : B → Type} {xs : List A}
  → (f : A → B)
  → (xs ↦′ C ∘ f)
  → (map f xs ↦′ C)
map-↦ f m y∈
  with _ , x∈ , refl ← L.Mem.∈-map⁻ f y∈
  = m x∈

map-↦˘ : ∀ {A B : Type} {C : B → Type} {xs : List A}
  → (f : A → B)
  → (map f xs ↦′ C)
  → (xs ↦′ C ∘ f)
map-↦˘ f = _∘ L.Mem.∈-map⁺ f

-- stipped version of `subterms`

record Strip (A : Type ℓ) : Type ℓ where
  field _∗ : Op₁ A
open Strip ⦃...⦄ public

instance
  Strip-D : Strip Branch
  Strip-D ._∗ = removeTopDecorations

{-
open import Prelude.Functor

private variable
  X Y : Type ℓ
  F : ∀ {ℓ} → Type ℓ → Type ℓ

instance
  Strip-List : ⦃ _ : Strip X ⦄ → ⦃ Functor F ⦄ → Strip (F X)
  Strip-List ⦃ sx ⦄ ._∗ = fmap (_∗ ⦃ sx ⦄)

  Strip-×² : ⦃ Strip Y ⦄ → Strip (X × Y)
  Strip-×² ⦃ sy ⦄ ._∗ = map₂ (_∗ ⦃ sy ⦄)
-}
  Strip-C : Strip Contract
  Strip-C ._∗ = map _∗

  Strip-V : Strip VContracts
  Strip-V ._∗ = map (map₂ _∗)
    where open import Prelude.Bifunctor


open Induction
module _ {X} ⦃ _ : Toℂ X ⦄ where
  subterms∗ : X → List Branch
  subterms∗ = _∗ ∘ subterms

open ≡-Reasoning

mutual
  subᵈ : subterms⁺ d ≡ d ∗ ∷ subterms∗ d
  subᵈ {d} with d
  ... | withdraw _               = refl
  ... | put _ &reveal _ if _ ⇒ c = cong (_ ∷_) $ subᶜ {c}
  ... | split vcs                = cong (_ ∷_) $ subᵛ {vcs}
  ... | _ ∶ d                    = subᵈ {d}
  ... | after _ ∶ d              = subᵈ {d}

  subᶜ : subterms⁺ c ≡ subterms∗ c
  subᶜ {[]}    = refl
  subᶜ {d ∷ c} =
    begin
      subterms⁺ d ++ subterms⁺ c
    ≡⟨ cong (_++ _) $ subᵈ {d} ⟩
      d ∗ ∷ subterms∗ d ++ subterms⁺ c
    ≡⟨ cong ((_ ∷ _) ++_) $ subᶜ {c} ⟩
      d ∗ ∷ subterms∗ d ++ subterms∗ c
    ≡⟨⟩
      d ∗ ∷ (subterms d) ∗ ++ (subterms c) ∗
    ≡˘⟨ cong (d ∗ ∷_) $ L.map-++-commute _∗ (subterms d) _ ⟩
      d ∗ ∷ (subterms d ++ subterms c) ∗
    ∎

  subᵛ : subterms⁺ vcs ≡ subterms∗ vcs
  subᵛ {[]} = refl
  subᵛ {(v , c) ∷ vcs} =
    begin
      subterms⁺ c ++ subterms⁺ vcs
    ≡⟨ cong (_++ _) $ subᶜ {c} ⟩
      subterms∗ c ++ subterms⁺ vcs
    ≡⟨ cong (_ ++_) $ subᵛ {vcs} ⟩
      subterms∗ c ++ subterms∗ vcs
    ≡˘⟨ L.map-++-commute _∗ (subterms c) _ ⟩
      (subterms c ++ subterms vcs) ∗
    ∎

weaken-sub+ : (subterms⁺ ad ↦′ BranchTx)
            → (subterms∗ ad ↦′ BranchTx)
weaken-sub+ {⟨ _ ⟩ c} = subst (_↦′ BranchTx) (subᶜ {c})

weaken-sub∗ : (subterms∗ ad ↦′ BranchTx)
            → (subterms  ad ↦′ BranchTx ∘ _∗)
weaken-sub∗ = map-↦˘ _∗

weaken-sub : (subterms⁺ ad ↦′ BranchTx)
           → (subterms  ad ↦′ BranchTx ∘ _∗)
weaken-sub {ad} = weaken-sub∗ {ad} ∘ weaken-sub+ {ad}
