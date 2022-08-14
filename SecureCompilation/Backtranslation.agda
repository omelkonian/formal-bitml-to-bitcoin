-- {-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init hiding (T)
open L.Mem using (_∈_; ∈-map⁻)
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Traces
open import Prelude.Membership hiding (_∈_)
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.InferenceRules
open import Prelude.Collections
open import Prelude.Semigroup
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Nary
open import Prelude.Apartness
open import Prelude.General

open import Bitcoin using (KeyPair)

module SecureCompilation.Backtranslation
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (Rˢ′; d)
open import ComputationalModel Participant Honest finPart keypairs as C
  hiding (Hon; Initial; Σ
         ; t; t′; `; ∣_∣; n)

open import SecureCompilation.Helpers  Participant Honest finPart keypairs η
open import SecureCompilation.Coherence Participant Honest finPart keypairs η as SC

postulate
  decode : Txout Rˢ → Message → Maybe Ad
  -- ^ decode bitstring as {G}C, converting outputs `txout(x)` to names `x`

  encode-decode : ∀ {Rˢ} (𝕣 : ℝ Rˢ) m → let open ℝ 𝕣 in
    ∀ ad →
      decode {Rˢ} txout′ m ≡ just ad
      ══════════════════════════════
      m ≡ encode {Rˢ} txout′ ad

try-decode : ∀ {Rˢ} (𝕣∗ : ℝ∗ Rˢ) m → let 𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣 in
    (∃ λ ad → m ≡ encode {Rˢ} txout′ ad)
  ⊎ (∀ ad → m ≢ encode {Rˢ} txout′ ad)
try-decode {Rˢ} 𝕣∗ m
  with 𝕣 ← ℝ∗⇒ℝ 𝕣∗
  with decode {Rˢ} (𝕣 .ℝ.txout′) m | encode-decode {Rˢ = Rˢ} 𝕣 m
... | just ad | p = inj₁ (ad , p ad .proj₁ refl)
... | nothing | p = inj₂ λ ad → λ where refl → case p ad .proj₂ refl of λ ()

{-
  ✓[1]: A →∗: C
  where
    ∙ C = encode {Rˢ} txout′ ⟨G⟩C
    ∙ Valid ⟨G⟩C
    ∙ Any (_∈ Hon) partG
    ∙ ⟨G⟩C ⊆⦅ deposits ⦆ Γ

  [2]: B →∗∶ SIGᵐ (K A) C,h̅,k̅
  where
    ∙ C = encode {Rˢ} txout′ ⟨G⟩C
    ∙ h̅ = map (proj₂ ∘ proj₂) Δ×h̅
    ∙ k̅ = concatMap (map pub ∘ codom) (codom k⃗)
    ∘ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C}

  [3]: B →∗∶ SIG (K̂ A) Tᵢₙᵢₜ

  [4]: submit Tᵢₙᵢₜ

  [5]: B →∗∶ SIGᵖ pubK T -- auth.control

  [6]: submit T -- put

  [7]: B →∗∶ ??? -- auth.reveal

  [8]: submit T -- split

  [9]: submit T -- withdraw

  [10]: B →∗∶ SIG (K̂ A) T -- auth.join

  [11]: submit T -- join

  [12]: B →∗∶ SIG (K̂ A) T -- auth.divide

  [13]: submit T -- divide

  [14]: B →∗∶ SIG (K̂ A) T -- auth.donate

  [15]: submit T -- donate

  [16]: B →∗∶ SIG (K̂ A) T -- auth.destroy

  [17]: submit T -- destroy

  ✓[18]: delay⦅ δ ⦆
-}

ℾ-∅ : ℾ ∅ᶜ
ℾ-∅ = record {txout = λ (); sechash = λ (); κ = λ ()}

∅ᵗ : Cfgᵗ
∅ᵗ = ∅ᶜ at 0

ℾᵗ-∅ᵗ : ℾᵗ ∅ᵗ
ℾᵗ-∅ᵗ = record {txout = λ (); sechash = λ (); κ = λ ()}

ℝ∗-∅ˢ : ℝ∗ ∅ˢ
ℝ∗-∅ˢ = ℾᵗ-∅ᵗ ∎⊣ auto ✓

module _ (Rˢ : S.Run) (𝕣∗ : ℝ∗ Rˢ) (Rᶜ : CRun) where
  𝕣 = ℝ∗⇒ℝ 𝕣∗
  open ℝ 𝕣

  module _ (A₀ : Participant) (m₀ : Message) where
    data DecodeBroadcastResponse : Set where

      [1] : ∀ ⟨G⟩C →
        ∙ Valid ⟨G⟩C
        ∙ Any (_∈ S.Hon) (nub-participants $ ⟨G⟩C .G)
        ∙ ⟨G⟩C ⊆⦅ deposits ⦆ (Rˢ ∙cfg)
        ∙ m₀ ≡ encode {Rˢ} txout′ ⟨G⟩C
          ───────────────────────────────────────────
          DecodeBroadcastResponse

      [2] : ∀ ⟨G⟩C (Δ×h̅ : List (Secret × Maybe ℕ × ℤ)) (k⃗ : 𝕂²′ ⟨G⟩C) A Γ₀ t →
        let
          ⟨ G ⟩ C = ⟨G⟩C
          Γ = ` ⟨G⟩C ∣ Γ₀
          Γₜ = Γ at t

          C : Message
          C = encode {Rˢ} txout′ ⟨G⟩C

          Δ : List (Secret × Maybe ℕ)
          Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

          (as , ms) = unzip Δ

          h̅ : List ℤ -- ≈ Message
          h̅ = map (proj₂ ∘ proj₂) Δ×h̅

          k̅ : List ℤ -- ≈ Message
          k̅ = concatMap (map pub ∘ codom) (codom k⃗)

          C,h̅,k̅ : Message
          C,h̅,k̅ = C ◇ h̅ ◇ k̅

          C,h̅,k̅ₐ : Message
          C,h̅,k̅ₐ = SIGᵐ (K A) C,h̅,k̅
        in
        ∙ Rˢ ≈⋯ Γₜ
        ∙ as ≡ secretsOfᵖ A G
        ∙ All (_∉ secretsOfᶜᶠ A Γ₀) as
        ∙ (A ∈ Hon → All Is-just ms)
        ∙ (∃ λ B → (B →∗∶ C) ∈ toList Rᶜ)
        ∙ All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅
        ∙ CheckOracleInteractions Rᶜ Δ×h̅
        ∙ Unique h̅
        ∙ Disjoint h̅ (codom sechash′)
        ∙ m₀ ≡ C,h̅,k̅ₐ
          ───────────────────────────────────────────
          DecodeBroadcastResponse

      [3] : ∀ (⟨G⟩C : Ad) Γ₀ t A v x →
          let ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG; Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = auth-init⦅ A , ⟨G⟩C , x ⦆
            Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (committedA : partG ⊆ committedParticipants ⟨G⟩C Γ₀)
          (A∈per : (A , v , x) ∈ persistentDeposits G)
        → let
            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

            open H₃ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x R≈ Γ→Γ′ ∃Γ≈ committedA using (T)
          in
        ∙ (∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ)
        ∙ m₀ ≡ [ SIG (K̂ A) T ]
          ───────────────────────────────────────────
          DecodeBroadcastResponse

      [5] : ∀ (⟨G⟩C : Ad) A v x Γ₀ t c (i : Index c) → let open ∣SELECT c i; Γ = ⟨ c , v ⟩at x ∣ Γ₀; Γₜ = Γ at t in
        (D≡A:D′ : A ∈ authDecorations d)
        (R≈ : Rˢ ≈⋯ Γₜ) →
        let
          α   = auth-control⦅ A , x ▷ d ⦆
          Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
          t′  = t
          Γₜ′ = Γ′ at t′

          ∃Γ≈ : ∃ (_≈ᶜ Γ′)
          ∃Γ≈ = Γ′ , ↭-refl

          Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
          Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

          open H₅ {Rˢ} 𝕣 t α t′ c v x Γ₀ A i R≈ Γ→Γ′ ∃Γ≈ D≡A:D′ using (T; pubK)
        in
        ∙ m₀ ≡ [ SIGᵖ pubK T ]
          ───────────────────────────────────────────
          DecodeBroadcastResponse

      [7] : ∀ {⟨G⟩C} A a n Γ₀ →
              let Γ = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀; Γₜ = Γ at t in
              ∀ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C in

          ∣ m ∣ᵐ ≤ η
        → (R≈ : Rˢ ≈⋯ Γₜ)

        → let
            C : Message
            C = encode {Rˢ = Rˢ} txout′ ⟨G⟩C

            Δ : List (Secret × Maybe ℕ)
            Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

            h̅ : Message
            h̅ = map (proj₂ ∘ proj₂) Δ×h̅

            k̅ : Message
            k̅ = concatMap (map pub ∘ codom) (codom k⃗)

            a∈ : a ∈ namesˡ Rˢ
            a∈ = namesˡ⦅end⦆⊆ Rˢ
                $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈) (here refl)

            C,h̅,k̅ : Message
            C,h̅,k̅ = C ◇ h̅ ◇ k̅
          in
            (∃ λ B → (B , m , [ sechash′ {a} a∈ ]) ∈ oracleInteractionsᶜ Rᶜ)
          → auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labels Rˢ
          → a ∈ namesˡ G
          → (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) (toList Rᶜ))
          → All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail ∃λ)
          → m₀ ≡ m
            -- ───────────────────────────────────────────
          → DecodeBroadcastResponse

      [10] : ∀ {A v x v′ x′ Γ₀ t} →
          let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = auth-join⦅ A , x ↔ x′ ⦆
            Γ′  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
            x∈′ = n⊆ (there $′ here refl)
          in
          (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                    → (l ≡ B →∗∶ [ T ♯ ])
                    × (inputs  T ≡ hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ [])
                    × (outputs T ≡ V.[ Ctx 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
                    ) (toList Rᶜ))
        → let
            T : ∃Tx
            T = 2 , 1 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

            m′ = [ SIG (K̂ A) T ]
            λᶜ = B →∗∶ m′
          in
        ∙ All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
        ∙ m₀ ≡ m′
          ──────────────────────────────────────────────────────────────────────────────────────
          DecodeBroadcastResponse

      [12] : ∀ {A v v′ x Γ₀} →
          let Γ = ⟨ A has (v + v′) ⟩at x ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
          in
          (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                    → (l ≡ B →∗∶ [ T ♯ ])
                    × (inputs  T ≡ V.[ hashTxⁱ (txout′ {x} x∈) ])
                    × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
                    ) (toList Rᶜ))
        → let
            T : ∃Tx
            T = 1 , 2 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

            m′ = [ SIG (K̂ A) T ]
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
        ∙ m₀ ≡ m′
          ────────────────────────────────────────────────────────────
          DecodeBroadcastResponse

      [14] : ∀ {A v x Γ₀ B′} →
          let Γ = ⟨ A has v ⟩at x ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
          in
          (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                    → (l ≡ B →∗∶ [ T ♯ ])
                    × (inputs  T ≡ V.[ hashTxⁱ (txout′ {x} x∈) ])
                    × (outputs T ≡ V.[ v -redeemableWith- K̂ B′ ])
                    ) (toList Rᶜ))
        → let
            T : ∃Tx
            T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

            m′ = [ SIG (K̂ A) T ]
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
        ∙ m₀ ≡ m′
          ────────────────────────────────────────────────────────────
          DecodeBroadcastResponse

      [16] : ∀ {ds : List (Participant × S.Value × Id)} {j : Index ds}
              {y : Id} {Γ₀ : Cfg} {B : Participant}

        → let
            xs = map (proj₂ ∘ proj₂) ds
            A  = proj₁ (ds ‼ j)
            j′ = ‼-map {xs = ds} j
            Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
            Γ  = Δ ∣ Γ₀
            Γₜ = Γ at t
          in
          (R≈ : Rˢ ≈⋯ Γₜ)
          (fresh-y : y ∉ ids Γ₀)
        → let
            α   = auth-destroy⦅ A , xs , j′ ⦆
            Γ′  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-AuthDestroy] fresh-y) refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₁₆ {Rˢ} 𝕣 t α t′ ds Γ₀  j A y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
          in
          (T : Tx i 0)
        → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)
        → (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ T ♯ ]) (toList Rᶜ))
        → let
            m = [ SIG (K̂ A) T ]
            λᶜ = B →∗∶ m
          in
          All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m) (Any-tail T∈)
        → (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
            → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
            → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓)) →
        ∙ A₀ ≡ B
        ∙ m₀ ≡ m
          ────────────────────────────────────────────────────────────
          DecodeBroadcastResponse

      FAIL :
        let λᶜ = A₀ →∗∶ m₀ in

        ∙ (∀ {Γₜ Rᶜ} (λˢ : 𝕃 Rˢ Γₜ) → (Γₜ ∷ 𝕣∗ ⊣ λˢ ✓) ≁₁ (λᶜ ∷ Rᶜ ✓))
          ────────────────────────────────────────────────────────────
          DecodeBroadcastResponse

    decodeBroadcast : DecodeBroadcastResponse
    decodeBroadcast = {!!}
    {-
        with try-decode {Rˢ = Rˢ} 𝕣∗ m
      ... | inj₂ m≢
      -- invalid [1]; ignore
        = {!!}
      ... | inj₁ (⟨G⟩C , refl)
      -- Hypotheses from [C-Advertise]
        with ¿ Valid ⟨G⟩C ¿
      ×-dec any? (_∈? S.Hon) (nub-participants (⟨G⟩C .G))
      ×-dec deposits ⟨G⟩C ⊆? deposits (Rˢ ∙cfg)
      ... | yes (vad , hon , d⊆)
    -}

  module _ (T₀ : ∃Tx) where

    data DecodeTxResponse : Set where

      [4] : ∀ (⟨G⟩C : Ad) (z : Id) (Γ₀ : Cfg) →
          let
            ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG
            toSpend = persistentDeposits G
            vs      = map select₂ toSpend
            xs      = map select₃ toSpend
            v       = sum vs

            Γ = ` ⟨G⟩C ∣ Γ₀
              ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ⟨G⟩C ] }) toSpend
              ∣ || map (_auth[ ♯▷ ⟨G⟩C ]) partG
            Γₜ = Γ at t
          in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = init⦅ G , C ⦆
            Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (fresh-z : z ∉ xs ++ ids Γ₀) →
          let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([C-Init] fresh-z) refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₄ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ toSpend v z R≈ Γ→Γ′ ∃Γ≈ using (T)
          in
        ∙ T₀ ≡ T
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      [6] :
          ∀ {ds : List (Participant × S.Value × Id)} {ss : List (Participant × Secret × ℕ)} →
          ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in
          ∀ {v y} → -- [T0D0] fixed in Agda-HEAD, see issue #5683
          let
            -- (i) xs = x₁⋯xₖ
            (_ , vs , xs) = unzip₃ ds
            (_ , as , _)  = unzip₃ ss
            Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
            Δ   = || map (uncurry₃ _∶_♯_) ss
            Γ₂  = Δ ∣ Γ₀
            Γ₁₂ = Γ₁ ∣ Γ₂
            Γ   = ⟨ c , v ⟩at y ∣ (Γ₁ ∣ Γ₂)
            Γₜ  = Γ at t
          in
          -- ii) in Rˢ, α consumes ⟨D+C,v⟩y and the deposits ⟨Aᵢ,vᵢ⟩ₓᵢ to produce ⟨C′,v′⟩y′
          --     where D = ⋯ : put⋯reveal⋯.C′
          --     let t be the maximum deadline in an `after` in front of D
          --     T0D0: what should t′ be in case there are no `after` decorations? (currently any value)
          (t≡ : t ≡ maximum t ts)
          (d≡ : d ≡⋯∶ put xs &reveal as if p ⇒ c′)
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = put⦅ xs , as , y ⦆
            Γ′  = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          -- Hypotheses from [C-PutRev]
          (fresh-y′ : y′ ∉ y L.∷ ids Γ₁₂)
          (p⟦Δ⟧≡ : S.⟦ p ⟧ Δ ≡ just true)
          -- Hypotheses from [Timeout]
          (As≡∅ : Null As)
        → let
            ∀≤t : All (_≤ t′) ts
            ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

            put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
            put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡ ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Timeout] As≡∅ ∀≤t put→ refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₆ {Rˢ} 𝕣 t α t′ c v y ds ss Γ₂ c′ y′ i p R≈ Γ→Γ′ ∃Γ≈ d≡ using (T)
          in
        ∙ T₀ ≡ T
          ──────────────────────────────────────────────────────────────
          DecodeTxResponse

      [8] :
          ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in
          ∀ {vcis : List (S.Value × Contracts × Id)} → let vs , cs , xs = unzip₃ vcis; v = sum vs in
          ∀ {y Γ₀} → -- [T0D0] fixed in Agda-HEAD, see issue #5683
          let Γ = ⟨ c , v ⟩at y ∣ Γ₀; Γₜ = Γ at t in

          -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨C₀,v₀⟩ₓ₀ | ⋯ | ⟨Cₖ,vₖ⟩ₓₖ
          --     where D = ⋯ : split vs → cs
          --     let t be the maximum deadline in an `after` in front of D
          --     T0D0: what should t′ be in case there are not after decorations? (currently any value)
          (t≡ : t ≡ maximum t ts)
          (d≡ : d ≡⋯∶ split (zip vs cs))
          (R≈ : Rˢ ≈⋯ Γₜ)
          -- Hypotheses from [C-Split]
          (fresh-xs : All (_∉ y L.∷ ids Γ₀) xs)
          -- Hypotheses from [Timeout]
          (As≡∅ : Null As)
        → let
            α   = split⦅ y ⦆
            Γ′  = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′

            ∀≤t : All (_≤ t′) ts
            ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

            split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
            split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
                  ~: [C-Split] {vcis = vcis} fresh-xs

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Timeout] As≡∅ ∀≤t split→ refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₈ {Rˢ} 𝕣 t α t′ c v y Γ₀ i vcis R≈ Γ→Γ′ ∃Γ≈ d≡ using (T)
          in
        ∙ T₀ ≡ T
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      [9] :
        ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in
        let Γ = ⟨ c , v ⟩at y ∣ Γ₀; Γₜ = Γ at t in

          -- (i) in Rˢ, α consumes ⟨D+C,v⟩y to obtain ⟨A,v⟩ₓ (where D = ⋯ : withdraw A)
          (d≡ : d ≡⋯∶ withdraw A)
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = withdraw⦅ A , v , y ⦆
            Γ′  = ⟨ A has v ⟩at x ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (fresh-x : x ∉ y L.∷ ids Γ₀)
          (As≡∅ : Null As)
          (∀≤t : All (_≤ t) ts)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Timeout] As≡∅ ∀≤t
              (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x)
              refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₉ {Rˢ} 𝕣 t α t′ c v y Γ₀ A x i R≈ Γ→Γ′ ∃Γ≈ d≡ using (T)
          in
        ∙ T₀ ≡ T
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      [11] :
          let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = join⦅ x ↔ x′ ⦆
            Γ′  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (fresh-y : y ∉ x L.∷ x′ ∷ ids Γ₀)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-Join] fresh-y) refl

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)
            x∈′ = n⊆ (there $′ here refl)

            T : ∃Tx
            T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
              { inputs  = hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ []
              ; wit     = wit⊥
              ; relLock = V.replicate 0
              ; outputs = V.[ (v + v′) -redeemableWith- K̂ A ]
              ; absLock = 0 }
          in
        ∙ T₀ ≡ T
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      [13] :
          let Γ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = divide⦅ x ▷ v , v′ ⦆
            Γ′  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (fresh-ys : All (_∉ x L.∷ ids Γ₀ ) (y ∷ y′ ∷ []))
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-Divide] fresh-ys) refl

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)

            T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
              { inputs  = V.[ hashTxⁱ (txout′ {x} x∈) ]
              ; wit     = wit⊥
              ; relLock = V.replicate 0
              ; outputs = (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ []
              ; absLock = 0 }
          in
        ∙ T₀ ≡ T
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      [15] :
          let Γ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀; Γₜ = Γ at t in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = donate⦅ x ▷ᵈ B′ ⦆
            Γ′  = ⟨ B′ has v ⟩at y ∣ Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′
          in
          (fresh-y : y ∉ x L.∷ ids Γ₀)
        → let
            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] ([DEP-Donate] fresh-y) refl

            n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
            n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
            x∈  = n⊆ (here refl)

            T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
              { inputs  = V.[ hashTxⁱ (txout′ {x} x∈) ]
              ; wit     = wit⊥
              ; relLock = V.replicate 0
              ; outputs = V.[ v -redeemableWith- K̂ B′ ]
              ; absLock = 0 }
          in
        ∙ T₀ ≡ T
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      [17] :
          ∀ {ds : List (Participant × S.Value × Id)} {j : Index ds}
        → let
            xs = map (proj₂ ∘ proj₂) ds
            Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                        (enumerate ds)
            Γ  = Δ ∣ Γ₀
            Γₜ = Γ at t
          in
          (R≈ : Rˢ ≈⋯ Γₜ)
        → let
            α   = destroy⦅ xs ⦆
            Γ′  = Γ₀
            t′  = t
            Γₜ′ = Γ′ at t′

            Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
            Γ→Γ′ = [Action] [DEP-Destroy] refl

            ∃Γ≈ : ∃ (_≈ᶜ Γ′)
            ∃Γ≈ = Γ′ , ↭-refl

            open H₁₇ {Rˢ} 𝕣 t α t′ ds Γ₀ y R≈ Γ→Γ′ ∃Γ≈ using (λˢ; xs↦)
          in
          (T : Tx i 0)
        → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)
        → let λᶜ = submit (-, -, T) in
          (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
            → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
            → (Γₜ′ ∷ 𝕣∗ ⊣ λˢ′ ✓) ≁₁₁ (λᶜ ∷ Rᶜ ✓))
        → T₀ ≡ (-, -, T)
          ────────────────────────────────────────────────────────────
          DecodeTxResponse

      FAIL :
        T₀ .proj₂ .proj₂ .inputs ♯ (hashTxⁱ <$> codom txout′)
        ────────────────────────────────────────────────────────────
        DecodeTxResponse

    decodeTx : DecodeTxResponse
    decodeTx = {!!}


parseRun : (Rᶜ : CRun) → ∃ (_~ Rᶜ)
parseRun (Rᶜ ∎⊣ init ✓) = ∅ˢ , ℝ∗-∅ˢ , base auto init (λ ())
parseRun ((A →O∶  m) ∷ Rᶜ ✓) =
  let Rˢ , 𝕣 , Rˢ~Rᶜ = parseRun Rᶜ
  in  Rˢ , 𝕣 , step₂ Rˢ~Rᶜ ([2] $′ inj₁ refl)
parseRun ((O→ A ∶ m) ∷ Rᶜ ✓) =
  let Rˢ , 𝕣 , Rˢ~Rᶜ = parseRun Rᶜ
  in  Rˢ , 𝕣 , step₂ Rˢ~Rᶜ ([2] $′ inj₂ refl)
parseRun (delay δ ∷ Rᶜ ✓)
  with δ >? 0
... | yes δ>0
  -- [18]
  = let
      Rˢ , 𝕣∗ , Rˢ~Rᶜ = parseRun Rᶜ
      𝕣 = ℝ∗⇒ℝ 𝕣∗; open ℝ 𝕣

      Γₜ@(Γ at t) = Rˢ .end
      α   = delay⦅ δ ⦆
      t′  = t + δ
      Γₜ′ = Γ at t′
      -- λᶜ  = delay δ

      ∃Γ≈ : ∃ (_≈ᶜ Γ)
      ∃Γ≈ = Γ , ↭-refl

      Γₜ″ = ∃Γ≈ .proj₁ at t′

      Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
      Γ→Γ′ = [Delay] δ>0

      open H₁₈ {Rˢ} 𝕣 t α t′ Γ (≈ᵗ-refl {Γₜ}) Γ→Γ′ ∃Γ≈ using (λˢ)
    in
      -, (Γₜ″ ∷ 𝕣∗ ⊣ λˢ ✓) , step₁ Rˢ~Rᶜ ([L] [18] δ>0 ∃Γ≈)
... | no  δ≯0
  -- invalid [18]; ignore
  -- cannot use [R] [3] as it only covers `A →∗∶ m` messages, not delays
  = {!!}

parseRun (submit T₀ ∷ Rᶜ ✓)
  with Rˢ , 𝕣∗ , Rˢ~Rᶜ ← parseRun Rᶜ
  with decodeTx Rˢ 𝕣∗ Rᶜ T₀
... | [4] ⟨G⟩C z Γ₀ R≈ fresh-z T≡ rewrite T≡ =
  let
    ⟨ G ⟩ C = ⟨G⟩C
    toSpend = persistentDeposits G
    vs      = map select₂ toSpend
    xs      = map select₃ toSpend
    v       = sum vs

    Γ′ = ⟨ C , v ⟩at z ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [4] R≈ ∃Γ≈ fresh-z)
... | [6] {Γ₀ = Γ₀} {c′ = c′} {y′ = y′} {ds = ds} {ss = ss} {v = v} t≡ d≡ R≈ fresh-y′ p⟦Δ⟧≡ As≡∅ refl =
  let
    (_ , vs , _) = unzip₃ ds
    (_ , as , _) = unzip₃ ss
    Δ  = || map (uncurry₃ _∶_♯_) ss
    Γ₂ = Δ ∣ Γ₀

    Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [6] t≡ d≡ R≈ ∃Γ≈ fresh-y′ p⟦Δ⟧≡ As≡∅)
... | [8] {vcis = vcis} {Γ₀ = Γ₀} t≡ d≡ R≈ fresh-xs As≡∅ refl =
  let
    Γ′ = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [8] t≡ d≡ R≈ fresh-xs As≡∅ ∃Γ≈)
... | [9] {v = v} {Γ₀ = Γ₀} {A = A} {x = x} d≡ R≈ frsg-x As≡∅ ∀≤t refl =
  let
    Γ′ = ⟨ A has v ⟩at x ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [9] d≡ R≈ ∃Γ≈ frsg-x As≡∅ ∀≤t)
... | [11] {A = A} {v = v} {v′ = v′} {Γ₀ = Γ₀} {y = y} R≈ fresh-y refl =
  let
    Γ′ = ⟨ A has (v + v′) ⟩at y ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [11] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y)
... | [13] {A = A} {v = v} {v′ = v′} {Γ₀ = Γ₀} {y = y} {y′ = y′} R≈ fresh-ys refl =
  let
    Γ′ = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [13] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-ys)
... | [15] {v = v} {B′ = B′} {Γ₀ = Γ₀} {y = y} R≈ fresh-y refl =
  let
    Γ′ = ⟨ B′ has v ⟩at y ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [15] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y)
... | [17] {Γ₀ = Γ₀} {j = j} R≈ T ⊆ins ¬coh refl =
  let
    Γ′ = Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([R] [17] {j = j} R≈ ∃Γ≈ T ⊆ins ¬coh)
... | FAIL ins♯ = -, 𝕣∗ , step₂ Rˢ~Rᶜ ([1] ins♯)

parseRun ((A₀ →∗∶ m₀) ∷ Rᶜ ✓)
  with Rˢ , 𝕣∗ , Rˢ~Rᶜ ← parseRun Rᶜ
  with decodeBroadcast Rˢ 𝕣∗ Rᶜ A₀ m₀
... | [1] ⟨G⟩C vad hon d⊆ refl =
  let
    Γₜ@(Γ at t) = Rˢ .end

    R≈ : Rˢ ≈⋯ Γₜ
    R≈ = refl , ↭-refl

    Γ′  = ` ⟨G⟩C ∣ Γ

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [1] {Γ = Γ} R≈ ∃Γ≈ vad hon d⊆)
... | [2] ⟨G⟩C Δ×h̅ k⃗ A Γ₀ t R≈ as≡ All∉ Hon⇒ ∃B h≡ h∈O unique-h h♯sechash refl =
  let
    Γ = ` ⟨G⟩C ∣ Γ₀
    Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅
    Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ
    Γ′  = Γ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [2] {Γ₀ = Γ₀} R≈ ∃Γ≈ as≡ All∉ Hon⇒ ∃B h≡ h∈O unique-h h♯sechash)
... | [3] ⟨G⟩C Γ₀ t A v x R≈ committedA A∈per ∃B refl =
  let
    Γ  = ` ⟨G⟩C ∣ Γ₀
    Γ′ = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [3] R≈ ∃Γ≈ committedA A∈per ∃B)
... | [5] ⟨G⟩C A v x Γ₀ t c i D≡A:D′ R≈ refl =
  let
    open ∣SELECT c i
    Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [5] D≡A:D′ R≈ ∃Γ≈)
... | [7] A a n Γ₀ m≤ R≈ ∃B ∃α a∈ ∃λ first-λᶜ refl =
  let
    Γ′  = A ∶ a ♯ n ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [7] {Γ₀ = Γ₀} m≤ R≈ ∃Γ≈ ∃B ∃α a∈ ∃λ first-λᶜ)
... | [10] {A = A}{v}{x}{v′}{x′}{Γ₀} R≈ ∃λ first-λᶜ refl =
  let
    Γ′ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [10] {Γ₀ = Γ₀} R≈ ∃Γ≈ ∃λ first-λᶜ)
... | [12] {A = A}{v}{v′}{x}{Γ₀} R≈ ∃λ first-λᶜ refl =
  let
    Γ′ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [12] {Γ₀ = Γ₀} R≈ ∃Γ≈ ∃λ first-λᶜ)
... | [14] {A = A}{v}{x}{Γ₀}{B′} R≈ ∃λ first-λᶜ refl =
  let
    Γ′ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([L] [14] {Γ₀ = Γ₀} R≈ ∃Γ≈ ∃λ first-λᶜ)
... | [16] {ds = ds}{j}{y}{Γ₀} R≈ fresh-y T ⊆ins T∈ first-λᶜ ¬coh refl refl =
  let
    xs = map (proj₂ ∘ proj₂) ds
    A  = proj₁ (ds ‼ j)
    j′ = ‼-map {xs = ds} j
    Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
    Γ′ = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀

    ∃Γ≈ : ∃ (_≈ᶜ Γ′)
    ∃Γ≈ = Γ′ , ↭-refl
  in
    -, -, step₁ Rˢ~Rᶜ ([R] [16] {Γ₀ = Γ₀} R≈ ∃Γ≈ fresh-y T ⊆ins T∈ first-λᶜ ¬coh)
... | FAIL ¬coh = -, 𝕣∗ , step₂ Rˢ~Rᶜ ([3] ¬coh)

--   ℵ : S.ParticipantStrategy A → C.ParticipantStrategy A
--   ℵ Σˢ = Σᶜ
--     where
--       go : C.Run → C.Labels
--       go Rᶜ =
--         let
--           Rᶜ∗ : C.Run
--           Rᶜ∗ = Rᶜ -- ∗

--           -- (1) parse the (stripped) run Rᶜ∗, so to obtain a corresponding
--           -- symbolic (stripped) run Rˢ∗
--           Rˢ∗ : S.Run
--           Rˢ∗ = parseRun Rᶜ∗

--           -- (3) evaluate Λˢ = Σˢ(Rˢ∗)
--           Λˢ : S.Labels
--           Λˢ = Σˢ .S.Σ Rˢ∗

--           -- (4) convert the symbolic actions Λˢ into computational actions Λᶜ
--           -- when Λˢ contains A:{G}C,Δ or A:{G}C,x follow stipulation protocol
--           Λᶜ : C.Labels
--           Λᶜ = flip map Λˢ $ λ where
--             auth-join⦅ A , x ↔ y ⦆        → {!!}
--             join⦅ x ↔ y ⦆                 → {!!}
--             auth-divide⦅ A , x ▷ v , v′ ⦆ → {!!}
--             divide⦅ A ▷ v , v′ ⦆          → {!!}
--             auth-donate⦅ A , x ▷ᵈ B ⦆     → {!!}
--             donate⦅ x ▷ᵈ B ⦆              → {!!}
--             auth-destroy⦅ A , xs , j ⦆    → {!!}
--             destroy⦅ xs ⦆                 → {!!}
--             advertise⦅ ad ⦆               → {!!}
--             auth-commit⦅ A , ad , Δ ⦆     → {!!}
--             auth-init⦅ A , ad , x ⦆       → {!!}
--             init⦅ G , C ⦆                 → {!!}
--             split⦅ y ⦆                    → {!!}
--             auth-rev⦅ A , a ⦆             → {!!}
--             put⦅ xs , as , y ⦆            → {!!}
--             withdraw⦅ A , v , y ⦆         → {!!}
--             auth-control⦅ A , x ▷ D ⦆     → {!!}
--             delay⦅ δ ⦆                    → {!!}
--         in
--           Λᶜ

--       Σᶜ : C.ParticipantStrategy A
--       Σᶜ = record {Σ = go}
