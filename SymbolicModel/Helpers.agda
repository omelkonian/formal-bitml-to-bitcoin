-- {-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- Helpers for stripping.
------------------------------------------------------------------------

open import Data.List using (length; map; concatMap; _++_; zip)
open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Nary

module SymbolicModel.Helpers
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import SymbolicModel.Strategy Participant Honest
  hiding ( _∎; begin_
         ; c; ad; g; Γ; Γ′; Δ; vs; xs; as
         )

open import Bitcoin.Crypto using (KeyPair)
open import Bitcoin.Tx.Base using (TxInput)


----

_≡⟨on:_⟩_ : ∀ {X : Set} → Configuration → (Configuration → X) → Configuration → Set
Γ ≡⟨on: f ⟩ Γ′ = f Γ ≡ f Γ′

_⊆⟨on:_⟩_ : ∀ {X : Set} → Configuration → (Configuration → List X) → Configuration → Set
Γ ⊆⟨on: f ⟩ Γ′ = f Γ ⊆ f Γ′

_≡⟨on:_⟩ʳ_ : ∀ {X : Set} → Run → (Run → X) → Run → Set
R ≡⟨on: f ⟩ʳ R′ = f R ≡ f R′

_⊆⟨on:_⟩ʳ_ : ∀ {X : Set} → Run → (Run → List X) → Run → Set
R ⊆⟨on: f ⟩ʳ R′ = f R ⊆ f R′

liftʳ : ∀ {Γ Γ′} R R′
  → Γ′ ≡⟨on: namesʳ ⟩ Γ
  → lastCfg R ≡ (Γ at t)
  → lastCfg R′ ≡ (Γ′ at t′)
  → R′ ≡⟨on: namesʳ ⟩ʳ R
liftʳ _ _ eq refl refl rewrite eq = refl

liftˡ : ∀ {Γ Γ′} R R′
  → Γ′ ≡⟨on: namesˡ ⟩ Γ
  → lastCfg R ≡ (Γ at t)
  → lastCfg R′ ≡ (Γ′ at t′)
  → R′ ≡⟨on: namesˡ ⟩ʳ R
liftˡ _ _ eq refl refl rewrite eq = refl

liftᵃ : ∀ {Γ Γ′} R R′
  → Γ′ ≡⟨on: authorizedHonAds ⟩ Γ
  → lastCfg R ≡ (Γ at t)
  → lastCfg R′ ≡ (Γ′ at t′)
  → R′ ≡⟨on: advertisements ⟩ʳ R
liftᵃ _ _ eq refl refl rewrite eq = refl

-- : ∀ {Γs : List Configuration}
--   → (∀ {Γ} → Γ ∈ Γs → Null $ collect Γ)
--   → Null $ collect (∣∣ Γs)


---

_↑_ : ∀ {A : Set} {P : A → Set} {xs xs′ : List A} → xs ↦′ P → xs′ ≡ xs → xs′ ↦′ P
f ↑ refl = f

cons-↦ : ∀ {A : Set} {P : A → Set} {xs : List A}
  → (x : A)
  → P x
  → xs ↦′ P
  → (x ∷ xs) ↦′ P
cons-↦ _ y _ (here refl) = y
cons-↦ _ _ f (there x∈)  = f x∈

𝕂′ : Advertisement → Set
𝕂′ (⟨ G ⟩ C) = subtermsᶜ′ C ↦ (nub-participants G ↦ KeyPair)

-- Txout Sechash 𝕂 : S.Run → Set
-- Txout   Rˢ = namesʳ Rˢ ↦ TxInput
-- Sechash Rˢ = namesˡ Rˢ ↦ ℤ
-- 𝕂       Rˢ = advertisements Rˢ ↦′ 𝕂′

Txout : ∀ {X} → ⦃ _ : X has Name ⦄ → Pred₀ X
Txout x = namesʳ x ↦ TxInput

Sechash : ∀ {X} → ⦃ _ : X has Name ⦄ → Pred₀ X
Sechash x = namesˡ x ↦ ℤ

𝕂 : ∀ {X} → ⦃ _ : X has Advertisement ⦄ → Pred₀ X
𝕂 x = advertisements x ↦′ 𝕂′

-----

module H₂ Γ B A ad (Δ : List (Secret × Maybe ℕ)) where
  private
    as = map proj₁ Δ
    Γ′ = Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ]

    hʳ : ∀ Δ → Null $ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
    hʳ [] = refl
    hʳ (_ ∷ []) = refl
    hʳ (_ ∷ Δ@(_ ∷ _)) rewrite hʳ Δ = L.++-identityʳ _

    hˡ : ∀ Δ → namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ) ≡ map proj₁ Δ
    hˡ [] = refl
    hˡ (_ ∷ []) = refl
    hˡ ((s , m) ∷ Δ@(_ ∷ _)) =
      begin
        namesˡ (⟨ B ∶ s ♯ m ⟩ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
      ≡⟨ mapMaybe-++ isInj₁ (names ⟨ B ∶ s ♯ m ⟩) (names $ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
        namesˡ ⟨ B ∶ s ♯ m ⟩ ++ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
      ≡⟨⟩
        s ∷ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
      ≡⟨ cong (s ∷_) (hˡ Δ) ⟩
        s ∷ map proj₁ Δ
      ∎ where open ≡-Reasoning

    hᵃ : ∀ Δ → Null $ authorizedHonAds (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
    hᵃ [] = refl
    hᵃ (_ ∷ []) = refl
    hᵃ (_ ∷ Δ@(_ ∷ _)) rewrite hᵃ Δ = L.++-identityʳ _

  namesʳ≡ : Γ′ ≡⟨on: namesʳ ⟩ Γ
  namesʳ≡ =
    begin
      namesʳ Γ′
    ≡⟨⟩
      namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ ∣ A auth[ ♯▷ ad ])
    ≡⟨ mapMaybe-++ isInj₂ (names (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)) (names (A auth[ ♯▷ ad ])) ⟩
      namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ namesʳ (A auth[ ♯▷ ad ])
    ≡⟨⟩
      namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ []
    ≡⟨ L.++-identityʳ _ ⟩
      namesʳ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
    ≡⟨ mapMaybe-++ isInj₂ (names Γ) (names (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)) ⟩
      namesʳ Γ ++ namesʳ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
    ≡⟨ cong (namesʳ Γ ++_) (hʳ Δ) ⟩
      namesʳ Γ ++ []
    ≡⟨ L.++-identityʳ _ ⟩
      namesʳ Γ
    ∎ where open ≡-Reasoning

  namesˡ≡ : namesˡ Γ′ ≡ namesˡ Γ ++ as
  namesˡ≡ =
    begin
      namesˡ Γ′
    ≡⟨ mapMaybe-++ isInj₁ (names $ Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) (names $ A auth[ ♯▷ ad ]) ⟩
      namesˡ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ++ []
    ≡⟨ L.++-identityʳ _ ⟩
      namesˡ (Γ ∣ || map (uncurry ⟨ B ∶_♯_⟩) Δ)
    ≡⟨ mapMaybe-++ isInj₁ (names Γ) (names $ || map (uncurry ⟨ B ∶_♯_⟩) Δ) ⟩
      namesˡ Γ ++ namesˡ (|| map (uncurry ⟨ B ∶_♯_⟩) Δ)
    ≡⟨ cong (namesˡ Γ ++_) (hˡ Δ) ⟩
      namesˡ Γ ++ as
    ∎ where open ≡-Reasoning

  ads≡ : authorizedHonAds Γ′ ≡ authorizedHonAds Γ ++ authorizedHonAds (A auth[ ♯▷ ad ])
  ads≡ rewrite hᵃ Δ | L.++-identityʳ (authorizedHonAds Γ) = refl

  module H₂′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

    txout↝ : Txout R → Txout R′
    txout↝ txout′ rewrite cfg≡ | cfg≡′ | namesʳ≡ = txout′

    sechash↝ : Sechash R → as ↦ ℤ → Sechash R′
    sechash↝ sechash′ f rewrite cfg≡ | cfg≡′ = extend-↦ (↭-reflexive namesˡ≡) sechash′ f

    κ↝ : 𝕂 R → (k⃗ : subtermsᶜ′ (C ad) ↦ (nub-participants (G ad) ↦ KeyPair)) → 𝕂 R′
    κ↝ κ′ k⃗ rewrite cfg≡ | cfg≡′ = extend-↦ (↭-reflexive ads≡) κ′ go
      where
        go : authorizedHonAds (A auth[ ♯▷ ad ]) ↦′ 𝕂′
        go x∈ with A ∈? Hon | x∈
        ... | yes _ | here refl = k⃗
        ... | no  _ | ()

module H₃ Γ A x ad where
  private
    Γ′ = Γ ∣ A auth[ x ▷ˢ ad ]

    names≡ : Γ′ ≡⟨on: names ⟩ Γ
    names≡ = L.++-identityʳ _

  namesʳ≡ : Γ′ ≡⟨on: namesʳ ⟩ Γ
  namesʳ≡ = cong filter₂ names≡

  namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
  namesˡ≡ = cong filter₁ names≡

  ads≡ : Γ′ ≡⟨on: authorizedHonAds ⟩ Γ
  ads≡ = L.++-identityʳ _

  module H₃′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′)
    Γ₀ (Γ≡ : Γ ≡ (` ad ∣ Γ₀))
    where

    txout↝ : Txout R → Txout R′
    txout↝ txout′ rewrite cfg≡ | cfg≡′ | namesʳ≡ = txout′

    sechash↝ : Sechash R → Sechash R′
    sechash↝ sechash′ rewrite cfg≡ | cfg≡′ | namesˡ≡ = sechash′

    κ↝ : 𝕂 R → 𝕂 R′
    κ↝ κ′ rewrite cfg≡ | cfg≡′ | ads≡ = κ′

    names⊆ : names (G ad) ⊆ names R
    names⊆ n∈ = ? -- rewrite cfg≡ | Γ≡ = {!!}


-- module H₄ G C v z Γ₀ (ds : List DepositRef) (ps : List Participant) where
--   private
--     ad = ⟨ G ⟩ C
--     Γ′ = ⟨ C , v ⟩at z ∣ Γ₀
--     Γ₁ = ` ad ∣ Γ₀
--     Γ₂ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) (ds)
--     Γ₃ = || map (_auth[ ♯▷ ad ]) (ps)
--     Γ  = Γ₁ ∣ Γ₂ ∣ Γ₃

--     h₀ : ∀ ps → Null $ namesʳ (|| map (_auth[ ♯▷ ad ]) ps)
--     h₀ [] = refl
--     h₀ (_ ∷ []) = refl
--     h₀ (_ ∷ ps@(_ ∷ _)) = h₀ ps

--     h₀′ : ∀ (ds : List DepositRef) →
--       namesʳ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds) ≡ map (proj₂ ∘ proj₂) ds
--     h₀′ [] = refl
--     h₀′ (_ ∷ []) = refl
--     h₀′ ((Aᵢ , vᵢ , xᵢ) ∷ ds@(_ ∷ _)) =
--       begin
--         namesʳ ((⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ∣ Γ″)
--       ≡⟨ mapMaybe-++ isInj₂ (names $ ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) (names Γ″) ⟩
--         namesʳ (⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ]) ++ namesʳ Γ″
--       ≡⟨ cong (_++ namesʳ Γ″) (mapMaybe-++ isInj₂ (names $ ⟨ Aᵢ has vᵢ ⟩at xᵢ) (names $ Aᵢ auth[ xᵢ ▷ˢ ad ])) ⟩
--         (xᵢ ∷ namesʳ (Aᵢ auth[ xᵢ ▷ˢ ad ])) ++ namesʳ Γ″
--       ≡⟨ cong (λ x → (xᵢ ∷ x) ++ namesʳ Γ″) (L.++-identityʳ _) ⟩
--         xᵢ ∷ namesʳ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds)
--       ≡⟨ cong (xᵢ ∷_) (h₀′ ds) ⟩
--         xᵢ ∷ map (proj₂ ∘ proj₂) ds
--       ∎ where open ≡-Reasoning
--               Γ″ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds

--     h₁ : ∀ (xs : List DepositRef) →
--       Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) xs)
--     h₁ [] = refl
--     h₁ (_ ∷ []) = refl
--     h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

--     h₂ : ∀ xs → Null $ namesˡ (|| map (_auth[ ♯▷ ad ]) xs)
--     h₂ [] = refl
--     h₂ (_ ∷ []) = refl
--     h₂ (_ ∷ xs@(_ ∷ _)) = h₂ xs

--     h₁′ : ∀ (xs : List DepositRef) →
--       Null $ authorizedHonAds (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) xs)
--     h₁′ [] = refl
--     h₁′ (_ ∷ []) = refl
--     h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

--   namesʳ≡₀ : namesʳ Γ ≡ namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
--   namesʳ≡₀ =
--     begin
--       namesʳ Γ
--     ≡⟨ mapMaybe-++ isInj₂ (names $ Γ₁ ∣ Γ₂) (names Γ₃) ⟩
--       namesʳ (Γ₁ ∣ Γ₂) ++ namesʳ Γ₃
--     ≡⟨ cong (namesʳ (Γ₁ ∣ Γ₂) ++_) (h₀ $ ps) ⟩
--       namesʳ (Γ₁ ∣ Γ₂) ++ []
--     ≡⟨ L.++-identityʳ _ ⟩
--       namesʳ (Γ₁ ∣ Γ₂)
--     ≡⟨ mapMaybe-++ isInj₂ (names $ Γ₁) (names Γ₂) ⟩
--       namesʳ Γ₁ ++ namesʳ Γ₂
--     ≡⟨ cong (_++ namesʳ Γ₂) (mapMaybe-++ isInj₂ (names $ ` ad) (names Γ₀)) ⟩
--       (namesʳ (` ad) ++ namesʳ Γ₀) ++ namesʳ Γ₂
--     ≡⟨⟩
--       namesʳ Γ₀ ++ namesʳ Γ₂
--     ≡⟨ cong (namesʳ Γ₀ ++_) (h₀′ ds) ⟩
--       namesʳ Γ₀ ++ map (proj₂ ∘ proj₂) ds
--     ∎ where open ≡-Reasoning


--   namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
--   namesˡ≡ = sym $
--     begin namesˡ Γ                      ≡⟨⟩
--           namesˡ (Γ₁ ∣ Γ₂ ∣ Γ₃)         ≡⟨ mapMaybe-++ isInj₁ (names $ Γ₁ ∣ Γ₂) (names Γ₃) ⟩
--           namesˡ (Γ₁ ∣ Γ₂) ++ namesˡ Γ₃ ≡⟨ cong (namesˡ (Γ₁ ∣ Γ₂)  ++_) (h₂ $ ps) ⟩
--           namesˡ (Γ₁ ∣ Γ₂) ++ []        ≡⟨ L.++-identityʳ _ ⟩
--           namesˡ (Γ₁ ∣ Γ₂)              ≡⟨ mapMaybe-++ isInj₁ (names Γ₁) (names Γ₂) ⟩
--           namesˡ Γ₁ ++ namesˡ Γ₂        ≡⟨ cong (namesˡ Γ₁ ++_) (h₁ ds) ⟩
--           namesˡ Γ₁ ++ []               ≡⟨ L.++-identityʳ _ ⟩
--           namesˡ Γ₁                     ≡⟨⟩
--           namesˡ Γ′                     ∎ where open ≡-Reasoning

--   ads⊆ : Γ′ ⊆⟨on: authorizedHonAds ⟩ Γ
--   ads⊆ = L.Mem.∈-++⁺ˡ ∘ L.Mem.∈-++⁺ˡ
--     {- T0D0: update to stdlib#v1.5 to fix `infixr step-⊆`
--     begin
--       authorizedHonAds Γ′
--     ≡⟨⟩
--       authorizedHonAds Γ₀
--     ⊆⟨ {!!} ⟩
--       authorizedHonAds Γ
--     ∎
--     where open ⊆-Reasoning Advertisement
--     -}

--   module H₄′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → TxInput → Txout R′
--     txout↝ txout′ tx rewrite cfg≡ | cfg≡′ | namesʳ≡₀ = cons-↦ z tx $ weaken-↦ txout′ L.Mem.∈-++⁺ˡ

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ | namesˡ≡ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = weaken-↦ κ′ ads⊆

-- module H₅ c v x Γ₀ A i where
--   private
--     Γ  = ⟨ c , v ⟩at x ∣ Γ₀
--     Γ′ = ⟨ c , v ⟩at x ∣ A auth[ x ▷ (c ‼ i) ] ∣ Γ₀

--   module H₅′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ = txout′

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₆ c v y c′ y′ (ds : List (Participant × Value × Id)) Γ₀ where
--   private
--     vs = proj₁ $ proj₂ $ unzip₃ ds
--     xs = proj₂ $ proj₂ $ unzip₃ ds
--     Γ₁ = || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds
--     Γ  = ⟨ c , v ⟩at y ∣ Γ₁ ∣ Γ₀
--     Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₀

--     h₁ : ∀ (ds : List (Participant × Value × Id)) →
--       Null $ namesˡ (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
--     h₁ [] = refl
--     h₁ (_ ∷ []) = refl
--     h₁ (_ ∷ xs@(_ ∷ _)) = h₁ xs

--     h₁′ : ∀ (ds : List (Participant × Value × Id)) →
--       Null $ authorizedHonAds (|| map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ }) ds)
--     h₁′ [] = refl
--     h₁′ (_ ∷ []) = refl
--     h₁′ (_ ∷ xs@(_ ∷ _)) = h₁′ xs

--   namesʳ≡₀ : namesʳ Γ ≡ (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
--   namesʳ≡₀ =
--     begin
--       namesʳ Γ
--     ≡⟨ mapMaybe-++ isInj₂ (inj₂ y ∷ names Γ₁) (names Γ₀) ⟩
--       (y ∷ namesʳ Γ₁) ++ namesʳ Γ₀
--     ∎ where open ≡-Reasoning

--   namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
--   namesˡ≡ =
--     begin
--       namesˡ Γ′
--     ≡⟨ mapMaybe-++ isInj₁ (names $ ⟨ c′ , v + sum vs ⟩at y′) (names Γ₀) ⟩
--       namesˡ (⟨ c′ , v + sum vs ⟩at y′) ++ namesˡ Γ₀
--     ≡⟨⟩
--       namesˡ Γ₀
--     ≡˘⟨ L.++-identityˡ _ ⟩
--       [] ++ namesˡ Γ₀
--     ≡˘⟨ cong (_++ namesˡ Γ₀) (h₁ ds) ⟩
--       namesˡ (⟨ c′ , v ⟩at y ∣ Γ₁) ++ namesˡ Γ₀
--     ≡˘⟨ mapMaybe-++ isInj₁ (names $ ⟨ c′ , v ⟩at y ∣ Γ₁) (names Γ₀) ⟩
--       namesˡ Γ
--     ∎ where open ≡-Reasoning

--   ads≡ : Γ′ ≡⟨on: authorizedHonAds ⟩ Γ
--   ads≡ =
--     begin
--       authorizedHonAds Γ′
--     ≡⟨⟩
--       authorizedHonAds Γ₀
--     ≡˘⟨ cong (_++ authorizedHonAds Γ₀) (h₁′ ds) ⟩
--       authorizedHonAds Γ₁ ++ authorizedHonAds Γ₀
--     ≡⟨⟩
--       authorizedHonAds Γ
--     ∎ where open ≡-Reasoning

--   module H₆′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → TxInput → Txout R′
--     txout↝ txout′ tx rewrite cfg≡ | cfg≡′ | namesʳ≡₀ = cons-↦ y′ tx $ weaken-↦ txout′ (L.Mem.∈-++⁺ʳ _)

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ | namesˡ≡ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡′ | cfg≡ | sym ads≡ = κ′

-- module H₇ A a n Γ₀ where
--   private
--     Γ  = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀
--     Γ′ = A ∶ a ♯ n ∣ Γ₀

--   module H₇′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ = txout′

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₈ c v y Γ₀ (vcis : List (Value × Contracts × Id)) where
--   private
--     xs = map (proj₂ ∘ proj₂) vcis
--     Γ₁ = || map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis
--     Γ  = ⟨ c , v ⟩at y ∣ Γ₀
--     Γ′ = Γ₁ ∣ Γ₀

--     hʳ : ∀ (vcis : List (Value × Contracts × Id)) →
--       namesʳ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis) ≡ map (proj₂ ∘ proj₂) vcis
--     hʳ [] = refl
--     hʳ (_ ∷ []) = refl
--     hʳ (_ ∷ xs@(_ ∷ _)) = cong (_ ∷_) (hʳ xs)

--     hˡ : ∀ (vcis : List (Value × Contracts × Id)) →
--       Null $ namesˡ (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
--     hˡ [] = refl
--     hˡ (_ ∷ []) = refl
--     hˡ (_ ∷ xs@(_ ∷ _)) = hˡ xs

--     hᵃ : ∀ (vcis : List (Value × Contracts × Id)) →
--       Null $ authorizedHonAds (|| map (λ{ (vᵢ , cᵢ , xᵢ) → ⟨ cᵢ , vᵢ ⟩at xᵢ }) vcis)
--     hᵃ [] = refl
--     hᵃ (_ ∷ []) = refl
--     hᵃ (_ ∷ xs@(_ ∷ _)) = hᵃ xs

--   namesʳ≡₀ : namesʳ Γ ≡ y ∷ namesʳ Γ₀
--   namesʳ≡₀ = mapMaybe-++ isInj₂ [ inj₂ y ] (names Γ₀)

--   namesʳ≡ : namesʳ Γ′ ≡ xs ++ namesʳ Γ₀
--   namesʳ≡ =
--     begin
--       namesʳ Γ′
--     ≡⟨ mapMaybe-++ isInj₂ (names Γ₁) (names Γ₀) ⟩
--       namesʳ Γ₁ ++ namesʳ Γ₀
--     ≡⟨ cong (_++ namesʳ Γ₀) (hʳ vcis) ⟩
--       xs ++ namesʳ Γ₀
--     ∎ where open ≡-Reasoning

--   namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
--   namesˡ≡ =
--     begin
--       namesˡ Γ′
--     ≡⟨ mapMaybe-++ isInj₁ (names Γ₁) (names Γ₀) ⟩
--       namesˡ Γ₁ ++ namesˡ Γ₀
--     ≡⟨ cong (_++ namesˡ Γ₀) (hˡ vcis) ⟩
--       namesˡ Γ₀
--     ≡⟨⟩
--       namesˡ Γ
--     ∎ where open ≡-Reasoning

--   ads≡ : Γ′ ≡⟨on: authorizedHonAds ⟩ Γ
--   ads≡ =
--     begin
--       authorizedHonAds Γ′
--     ≡⟨ cong (_++ authorizedHonAds Γ₀) (hᵃ vcis) ⟩
--       authorizedHonAds Γ₀
--     ≡⟨⟩
--       authorizedHonAds Γ
--     ∎ where open ≡-Reasoning

--   module H₈′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → (xs ↦ TxInput) → Txout R′
--     txout↝ txout′ f rewrite cfg≡ | cfg≡′ | namesʳ≡₀ = extend-↦ (↭-reflexive namesʳ≡) f (weaken-↦ txout′ there)

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ | namesˡ≡ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ | ads≡ = κ′

-- module H₉ c v y Γ₀ A x where
--   private
--     Γ  = ⟨ c , v ⟩at y ∣ Γ₀
--     Γ′ = ⟨ A has v ⟩at x ∣ Γ₀

--   module H₉′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → TxInput → Txout R′
--     txout↝ txout′ tx rewrite cfg≡ | cfg≡′ = cons-↦ x tx $ weaken-↦ txout′ there

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₀ A v x v′ x′ Γ₀ where
--   private
--     Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀
--     Γ′ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀

--   module H₁₀′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ = txout′

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₁ A v x v′ x′ y Γ₀ where
--   private
--     Γ  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
--     Γ′ = ⟨ A has (v + v′) ⟩at y ∣ Γ₀

--   module H₁₁′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → TxInput → Txout R′
--     txout↝ txout′ tx rewrite cfg≡ | cfg≡′ = cons-↦ y tx $ weaken-↦ txout′ (λ x∈ → there (there x∈))

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₂ A v v′ x Γ₀ where
--   private
--     Γ  = ⟨ A has (v + v′) ⟩at x ∣ Γ₀
--     Γ′ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀

--   module H₁₂′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ = txout′

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₃ A v v′ x Γ₀ y y′ where
--   private
--     Γ  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
--     Γ′ = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀

--   module H₁₃′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → TxInput × TxInput → Txout R′
--     txout↝ txout′ (tx , tx′) rewrite cfg≡ | cfg≡′ = cons-↦ y tx $ cons-↦ y′ tx′ $ weaken-↦ txout′ there

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₄ A v x Γ₀ B′ where
--   private
--     Γ  = ⟨ A has v ⟩at x ∣ Γ₀
--     Γ′ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀

--   module H₁₄′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ = txout′

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₅ A v x B′ Γ₀ y where
--   private
--     Γ  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
--     Γ′ = ⟨ B′ has v ⟩at y ∣ Γ₀

--   module H₁₅′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → TxInput → Txout R′
--     txout↝ txout′ tx rewrite cfg≡ | cfg≡′ = cons-↦ y tx $ weaken-↦ txout′ there

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = κ′

-- module H₁₆ (ds : List (Participant × Value × Id)) (j : Index ds) Γ₀ A y where
--   private
--     xs = map (proj₂ ∘ proj₂) ds
--     j′ = Index xs ∋ ‼-map {xs = ds} j
--     Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
--     Γ  = Δ ∣ Γ₀
--     Γ′ = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀

--     names≡ : Γ′ ≡⟨on: names ⟩ Γ
--     names≡ rewrite L.++-identityʳ (names Δ) = refl

--   namesʳ≡ :  Γ′ ≡⟨on: namesʳ ⟩ Γ
--   namesʳ≡ = cong filter₂ names≡

--   namesˡ≡ : Γ′ ≡⟨on: namesˡ ⟩ Γ
--   namesˡ≡ = cong filter₁ names≡

--   ads≡ : Γ′ ≡⟨on: authorizedHonAds ⟩ Γ
--   ads≡ rewrite L.++-identityʳ (authorizedHonAds Δ) = refl

--   module H₁₆′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ | namesʳ≡ = txout′

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ | namesˡ≡ = sechash′

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ | ads≡ = κ′

-- module H₁₇ (ds : List (Participant × Value × Id)) Γ₀ y where
--   private
--     xs = map (proj₂ ∘ proj₂) ds
--     Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] }) (enumerate ds)
--     Γ  = Δ ∣ Γ₀
--     Γ′ = Γ₀

--   namesˡ≡₀ : namesˡ Γ ≡ namesˡ Δ ++ namesˡ Γ₀
--   namesˡ≡₀ = mapMaybe-++ isInj₁ (names Δ) (names Γ₀)

--   namesʳ≡₀ : namesʳ Γ ≡ namesʳ Δ ++ namesʳ Γ₀
--   namesʳ≡₀ = mapMaybe-++ isInj₂ (names Δ) (names Γ₀)

--   module H₁₇′ R R′ (cfg≡ : cfg (lastCfg R) ≡ Γ) (cfg≡′ : cfg (lastCfg R′) ≡ Γ′) where

--     txout↝ : Txout R → Txout R′
--     txout↝ txout′ rewrite cfg≡ | cfg≡′ | namesʳ≡₀ = weaken-↦ txout′ (L.Mem.∈-++⁺ʳ _)

--     sechash↝ : Sechash R → Sechash R′
--     sechash↝ sechash′ rewrite cfg≡ | cfg≡′ | namesˡ≡₀ = weaken-↦ sechash′ (L.Mem.∈-++⁺ʳ _)

--     κ↝ : 𝕂 R → 𝕂 R′
--     κ↝ κ′ rewrite cfg≡ | cfg≡′ = weaken-↦ κ′ (L.Mem.∈-++⁺ʳ _)

-- {-
-- variable
--   Δ : Configuration′ Iᶜᶠ[ [] & rads , [] & [] , [] & [] ]
--   Δs : List (Configuration Iᶜᶠ[ [] , [] , [] ])

--   R R′ R″ : Run
--   T T′ T″ : ∃TimedConfiguration

--   c : Contracts ci

--   ps : List Participant
--   ss : List ValidSecret


-- strip-cases-helper : ((ci , c) ∷ cs′ ∣∣ᶜˢ Γ) ∗ᶜ
--                    ≡ (  ⟨ c ⟩ᶜ
--                      ∣∣ (cs′ ∣∣ᶜˢ Γ) ∗ᶜ
--                      ∶- refl & refl & refl & (\\-left {[ ci , c ]}) & refl & refl )
-- strip-cases-helper = refl

-- strip-cases : (cs′ ∣∣ᶜˢ Γ) ∗ᶜ ≡ (cs′ ∣∣ᶜˢ (Γ ∗ᶜ))
-- strip-cases {cs′ = []} = refl
-- strip-cases {cs′ = (ci , c) ∷ cs′} {ads} {cs} {ds} {Γ}
--   rewrite strip-cases-helper {ci} {c} {cs′} {ads} {cs} {ds} {Γ}
--         | strip-cases {cs′} {ads} {cs} {ds} {Γ}
--         = refl

-- strip-ds : (ds′ ∣∣ᵈˢ Γ) ∗ᶜ ≡ (ds′ ∣∣ᵈˢ Γ ∗ᶜ)
-- strip-ds {ds′ = []} = refl
-- strip-ds {ds′ = d ∷ ds′} {Γ = Γ}
--   rewrite strip-ds {ds′} {Γ = Γ} = refl

-- strip-ss : (ss ∣∣ˢˢ Γ) ∗ᶜ ≡ (ss ∣∣ˢˢ Γ ∗ᶜ)
-- strip-ss {ss = []} = refl
-- strip-ss {ss = s ∷ ss} {Γ = Γ}
--   rewrite strip-ss {ss = ss} {Γ = Γ} = refl

-- strip-b : ∀ {i j} →
--   (Γ ∣∣ᵇ (i , j , ps)) ∗ᶜ ≡ (Γ ∗ᶜ ∣∣ᵇ (i , j , ps))
-- strip-b {ps = []} = refl
-- strip-b {ps = p ∷ ps} = strip-b {ps = ps}

-- strip-committedParticipants : committedParticipants (Γp ∗ᶜ) ad
--                             ≡ committedParticipants Γp ad
-- strip-committedParticipants {Γp = ∅ᶜ}              = refl
-- strip-committedParticipants {Γp = ` _}             = refl
-- strip-committedParticipants {Γp = ⟨ _ ⟩ᶜ}          = refl
-- strip-committedParticipants {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
-- strip-committedParticipants {Γp = _ auth[ _ ]∶- _} = refl
-- strip-committedParticipants {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
-- strip-committedParticipants {Γp = _ ∶ _ ♯ _}       = refl
-- strip-committedParticipants {Γp = l ∣∣ r ∶- _} {ad = ad}
--   rewrite strip-committedParticipants {Γp = l} {ad = ad}
--         | strip-committedParticipants {Γp = r} {ad = ad}
--         = refl

-- strip-committedParticipants₂ :
--     All (λ p → p ∈ committedParticipants Γp ad)                ps
--   → All (λ p → p ∈ committedParticipants (Γp ∗ᶜ) ad) ps
-- strip-committedParticipants₂ {Γp = Γp} {ad = ad} p
--   rewrite strip-committedParticipants {Γp = Γp} {ad = ad} = p

-- strip-spentForStipulation : spentForStipulation (Γp ∗ᶜ) ad
--                           ≡ spentForStipulation Γp ad
-- strip-spentForStipulation {Γp = ∅ᶜ}              = refl
-- strip-spentForStipulation {Γp = ` _}             = refl
-- strip-spentForStipulation {Γp = ⟨ _ ⟩ᶜ}          = refl
-- strip-spentForStipulation {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
-- strip-spentForStipulation {Γp = _ auth[ _ ]∶- _} = refl
-- strip-spentForStipulation {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
-- strip-spentForStipulation {Γp = _ ∶ _ ♯ _}       = refl
-- strip-spentForStipulation {Γp = l ∣∣ r ∶- _} {ad = ad}
--   rewrite strip-spentForStipulation {Γp = l} {ad = ad}
--         | strip-spentForStipulation {Γp = r} {ad = ad}
--         = refl

-- strip-spentForStipulation₂ : toStipulate (G ad) ≡ spentForStipulation Δ ad
--                            → toStipulate (G ad) ≡ spentForStipulation (Δ ∗ᶜ) ad
-- strip-spentForStipulation₂ {ad = ad} {Δ = Δ} p
--   rewrite strip-spentForStipulation {Γp = Δ} {ad = ad} = p


-- open import Data.List.Properties using (map-++-commute)
-- strip-cfgToList :
--   cfgToList (Γp ∗ᶜ) ≡ map (map₂ _∗ᶜ) (cfgToList Γp)
-- strip-cfgToList {Γp = ∅ᶜ}              = refl
-- strip-cfgToList {Γp = ` _}             = refl
-- strip-cfgToList {Γp = ⟨ _ ⟩ᶜ}          = refl
-- strip-cfgToList {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
-- strip-cfgToList {Γp = _ auth[ _ ]∶- _} = refl
-- strip-cfgToList {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
-- strip-cfgToList {Γp = _ ∶ _ ♯ _}       = refl
-- strip-cfgToList {Γp = l ∣∣ r ∶- _}
--   rewrite strip-cfgToList {Γp = l}
--         | strip-cfgToList {Γp = r}
--         = sym (map-++-commute (map₂ _∗ᶜ) (cfgToList l) (cfgToList r))

-- open import Data.List.Relation.Binary.Permutation.Inductive.Properties using (map⁺)
-- strip-≈ : Γp    ≈ Γp′
--         → Γp ∗ᶜ ≈ Γp′ ∗ᶜ
-- strip-≈ {Γp = Γp} {Γp′ = Γp′} Γp≈
--   rewrite strip-cfgToList {Γp = Γp}
--         | strip-cfgToList {Γp = Γp′}
--         = map⁺ (map₂ _∗ᶜ) Γp≈

-- strip-lastCfg : lastCfg (R ∗) ≡ (lastCfg R) ∗ᵗ
-- strip-lastCfg {_ ∙ˢ}        = refl
-- strip-lastCfg {_ ∷ˢ⟦ _ ⟧ _} = refl

-- strip-idempotent : ∀ (γ : Configuration′ cf′i) →
--   (γ ∗ᶜ) ∗ᶜ ≡ γ ∗ᶜ
-- strip-idempotent ∅ᶜ                = refl
-- strip-idempotent (` _)             = refl
-- strip-idempotent ⟨ _ ⟩ᶜ            = refl
-- strip-idempotent ⟨ _ , _ ⟩ᵈ        = refl
-- strip-idempotent (_ auth[ _ ]∶- _) = refl
-- strip-idempotent ⟨ _ ∶ _ ♯ _ ⟩     = refl
-- strip-idempotent (_ ∶ _ ♯ _)       = refl
-- strip-idempotent (l ∣∣ r ∶- _)     rewrite strip-idempotent l
--                                         | strip-idempotent r
--                                         = refl

-- strip-strip-rewrite : ∀ {l : Configuration Iᶜᶠ[ ads , cs , ds ]} {γ : Configuration Iᶜᶠ[ ads′ , cs′ , ds′ ]} {pr}
--   → (_∣∣_∶-_ {ads = ads ++ ads′} {rads = []}
--              {cs = cs  ++ cs′} {rcs = []}
--              {ds = ds ++ ds′} {rds = []}
--              l ((γ ∗ᶜ) ∗ᶜ) pr)
--   ≡ (l ∣∣ γ ∗ᶜ ∶- pr)
-- strip-strip-rewrite {γ = γ}
--   rewrite strip-idempotent γ
--         = refl

-- help : R ∗ ——→[ α ] T′
--      → proj₂ ((lastCfg R) ∗ᵗ) —→ₜ[ α ] proj₂ T′
-- help {R = _ ∙ˢ}        R→ = R→
-- help {R = _ ∷ˢ⟦ _ ⟧ _} R→ = R→

-- destruct-γ∗ : ∀ {Γ Γ₀ : Configuration′ Iᶜᶠ[ ads & rads , cs & rcs , ds & rds ]}
--                 {l    : Configuration Iᶜᶠ[ ads′ , cs′ , ds′ ]}
--                 {γ∗   : Configuration′ Iᶜᶠ[ adsʳ & radsʳ , csʳ & rcsʳ , dsʳ & rdsʳ ]}
--                 {pr   : ads  ≡ ads′ ++ adsʳ
--                       × rads ≡ [] ++ (radsʳ \\ ads′)
--                       × cs   ≡ cs′  ++ csʳ
--                       × rcs  ≡ [] ++ (rcsʳ \\ cs′)
--                       × ds   ≡ (ds′ \\ rdsʳ) ++ dsʳ
--                       × rds  ≡ [] ++ (rdsʳ \\ ds′) }
--   → Γ₀ ≡ Γ ∗ᶜ
--   → Γ₀ ≡ (l ∗ᶜ ∣∣ γ∗ ∶- pr)
--   → ∃[ γ ] ( (γ∗ ≡ γ ∗ᶜ)
--            × (Γ ≡ (l ∣∣ γ ∶- pr)) )
-- destruct-γ∗ {Γ = ∅ᶜ}              refl ()
-- destruct-γ∗ {Γ = ` _}             refl ()
-- destruct-γ∗ {Γ = ⟨ _ ⟩ᶜ}          refl ()
-- destruct-γ∗ {Γ = ⟨ _ , _ ⟩ᵈ}      refl ()
-- destruct-γ∗ {Γ = _ auth[ _ ]∶- _} refl ()
-- destruct-γ∗ {Γ = ⟨ _ ∶ _ ♯ _ ⟩}   refl ()
-- destruct-γ∗ {Γ = _ ∶ _ ♯ _}       refl ()
-- destruct-γ∗ {Γ = l′ ∣∣ γ ∶- pr₂} {Γ₀ = Γ₀} {l = l} {γ∗ = γ∗} {pr = pr₁} p0 p
--   with pr₁
-- ... | (refl , refl , refl , refl , refl , refl)
--     = {! γ , refl , refl !}

-- data Singleton {a} {A : Set a} (x : A) : Set a where
--   _with≡_ : (y : A) → x ≡ y → Singleton x

-- inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
-- inspect x = x with≡ refl

-- -}
