open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Bifunctor
open import Prelude.Traces
open import Prelude.ToList
open import Prelude.Setoid
open import Prelude.Membership
open import Prelude.InferenceRules

open import BitML.BasicTypes using (⋯)

module SymbolicModel.Run.Properties (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML ⋯
open import SymbolicModel.Run.Base ⋯

start∈allCfgsᵗ : R .start ∈ allTCfgs⁺ R
start∈allCfgsᵗ {R = record {trace = _ , Γ↞}} with Γ↞
... | _ ∎              = here refl
... | _ —→⟨ _ ⟩ _ ⊢ tr = here refl

end∈allCfgsᵗ : ∀ R → R .end ∈ allTCfgs⁺ R
end∈allCfgsᵗ = go ∘ _∙trace′
  module ⟫end∈allCfgsᵗ where
    go : (tr : Γₜ —[ αs ]↠ₜ Γₜ′) → Γₜ′ ∈ allStatesᵗ⁺ tr
    go (_ ∎)              = here refl
    go (_ —→⟨ _ ⟩ _ ⊢ tr) = there (go tr)

allTCfgs≡ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → allTCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ allTCfgs R ∷ʳ Γₜ
allTCfgs≡  {α}{Γₜ′}{Γₜ}{R@(record {trace = _ , Γ↞})}{x} Γ← eq =
  begin≡
    allTCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    toList (allTCfgs⁺ $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    toList (allStatesᵗ⁺ $ Γₜ `⟨ Γ← ⟩←—ₜ eq ⊢ Γ↞)
  ≡⟨ cong toList $ allStatesᵗ⁺-∷ʳ Γ↞ Γ← eq ⟩
    toList (allStatesᵗ⁺ Γ↞ ⁺∷ʳ Γₜ)
  ≡⟨⟩
    allTCfgs R ∷ʳ Γₜ
  ∎≡ where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

allCfgs≡ : ∀ {x}
  → (Γ← : x —[ α ]→ₜ Γₜ′)
  → (eq : Γₜ ≈ Γₜ′ × R .end ≈ x)
  → allCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡ allCfgs R ∷ʳ cfg Γₜ
allCfgs≡  {α}{Γₜ′}{Γₜ}{R@(record {trace = _ , Γ↞})}{x} Γ← eq =
  begin≡
    allCfgs (Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨⟩
    map cfg (allTCfgs $ Γₜ ⟨ Γ← ⟩←—— R ⊣ eq)
  ≡⟨ cong (map cfg) (allTCfgs≡ {R = R} Γ← eq) ⟩
    map cfg (allTCfgs R ∷ʳ Γₜ)
  ≡⟨ L.map-++-commute cfg (allTCfgs R) [ Γₜ ] ⟩
    map cfg (allTCfgs R) ++ [ cfg Γₜ ]
  ≡⟨⟩
    allCfgs R ∷ʳ cfg Γₜ
  ∎≡
  where open ≡-Reasoning renaming (begin_ to begin≡_; _∎ to _∎≡)

∃[_∋ʳ_] : Run → Rel₀ Cfg → Set
∃[ R ∋ʳ P ] = ∃[ R ∙trace′ ∋ P ]

ad∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ ` ad ∈ᶜ Γ
    ───────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-Advertise]⦅_↝_⦆⦅ ad ⦆ ]
ad∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) ad∈ =
  traceAd∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) ad∈) tr

ad∈≈⇒ℍ′ :
  ∙ (Γ , Γ′) ⋯∈ R
  ∙ ` ad ∈ᶜ Γ
    ───────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-Advertise]⦅_↝_⦆⦅ ad ⦆ ]
ad∈≈⇒ℍ′ {Γ}{_}{R@record {init = i , _; trace = _ , tr}}{ad} xy∈ ad∈ =
  let
    xy∈ᵗ = ×∈⇒×∈ᵗ tr xy∈ .proj₂ .proj₂
    tr  = R ∙trace′
    tr′ = splitTraceˡ tr xy∈ᵗ
  in
    ∃-weaken∈ tr′ tr (⊆ᵗʳ-splitTraceˡ tr xy∈ᵗ) $ traceAd∗ i ad∈ tr′

auth-commit∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ A auth[ ♯▷ ad ] ∈ᶜ Γ
    ────────────────────────────────────────────────────
    ∃ λ Δ → ∃[ R ∋ʳ ℍ[C-AuthCommit]⦅_↝_⦆⦅ ad , A , Δ ⦆ ]
auth-commit∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  traceAuthCommit∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

auth-commit∈≈⇒ℍ′ :
  ∙ (Γ , Γ′) ⋯∈ R
  ∙ A auth[ ♯▷ ad ] ∈ᶜ Γ
    ────────────────────────────────────────────────────
    ∃ λ Δ → ∃[ R ∋ʳ ℍ[C-AuthCommit]⦅_↝_⦆⦅ ad , A , Δ ⦆ ]
auth-commit∈≈⇒ℍ′ {Γ}{_}{R@record {init = i , _; trace = _ , tr}} xy∈ auth∈ =
  let
    xy∈ᵗ = ×∈⇒×∈ᵗ tr xy∈ .proj₂ .proj₂
    tr′  = splitTraceˡ tr xy∈ᵗ
  in
    map₂′ (∃-weaken∈ tr′ tr (⊆ᵗʳ-splitTraceˡ tr xy∈ᵗ))
          (traceAuthCommit∗ i auth∈ tr′)

auth-init∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ A auth[ z ▷ˢ ad ] ∈ᶜ Γ
    ──────────────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-AuthInit]⦅_↝_⦆⦅ A , ad , z ⦆ ]
auth-init∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  traceAuthInit∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

auth-control∈≈⇒ℍ :
  ∙ R ≈⋯ Γ at t
  ∙ A auth[ z ▷ d ] ∈ᶜ Γ
    ────────────────────────────────────────────
    ∃[ R ∋ʳ ℍ[C-AuthControl]⦅_↝_⦆⦅ A , z , d ⦆ ]
auth-control∈≈⇒ℍ {R@record {init = i , _; trace = _ , tr}}{Γ} (_ , Γ≈) auth∈ =
  traceAuthControl∗ i (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) auth∈) tr

c∈≈⇒Ancestor :
  ∙ R ≈⋯ Γ at t
  ∙ ⟨ c , v ⟩at x ∈ᶜ Γ
    ─────────────────────────────────────
    ∃ λ ad → ∃[ R ∋ʳ Ancestor⦅ ad ↝ c ⦆ ]
c∈≈⇒Ancestor {R@record {init = i , t≡0; trace = _ , tr}}{Γ}{t}{c} (_ , Γ≈) c∈ =
  traceContract∗ i t≡0 (∈ᶜ-resp-≈ {Γ}{cfg $ R .end} (↭-sym Γ≈) c∈) tr
