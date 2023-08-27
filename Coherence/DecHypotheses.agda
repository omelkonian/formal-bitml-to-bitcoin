open import Prelude.Init hiding (T) renaming (toWitness to _¡)
open SetAsType
open L.Mem
open L.All using (lookup; ¬Any⇒All¬)
open L.Any using (satisfied; lookup-index)
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Membership.Patterns
open import Prelude.Lists
open import Prelude.Lists.Collections
open import Prelude.Lists.Dec
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Traces
open import Prelude.Null
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.ToList
open import Prelude.Functor
open import Prelude.Decidable
open import Prelude.Num

open import SecureCompilation.ModuleParameters using (⋯)
module Coherence.DecHypotheses (⋯ : ⋯) (let open ⋯ ⋯) where

open import SymbolicModel ⋯′ as S
  hiding ( _∎; begin_
         {-variables-}
         ; Γ₀; Γ; Γ′; Γ″; Γₜ; Γₜ′; Γₜ″; Δ
         ; R; R′; Rˢ; Rˢ′
         ; A; B; B′
         ; G; C
         ; t; t′; δ; n
         ; ad; g; c; c′; cs; ds; d; vcs
         ; x; x′; y; y′; z; xs
         ; a; as
         ; v; v′; vs
         ; α; p; Σ
         )
open import ComputationalModel ⋯′ finPart keypairs
  hiding ( `; ∣_∣; _`∧_; _`∨_; _`=_; _`<_; `true; ∎
         ; Run; Time; Value; DecEq-Label
         ; HonestMoves; HonestStrategies; ParticipantStrategy
         ; Valid-Strategy; moves
         ; Σ
         ; module AdvM
         {-variables-}
         ; R; R′; R″; Rᶜ
         ; tx; i; t; t′; n; m; m′; λᶜ
         )
  renaming (Label to CLabel; Labels to CLabels)
open import Compiler ⋯′ η
open import Coherence.ComputationalContracts ⋯′
open import Coherence.Helpers ⋯
open import Coherence.Hypotheses ⋯

-- shorthands
record ℍ-Run? {Γₜ α Γₜ′} (Γ→ : Γₜ —[ α ]→ₜ Γₜ′) ($Γ″ : Cfg) : Type where
  constructor mk?
  Γ″ = $Γ″
  private Γ′ = Γₜ′ .cfg; t′ = Γₜ′ .time
  field
    {Rᶜ} : CRun
    {Rˢ} : Run
    {𝕣∗} : ℝ∗ Rˢ
    {R≈?} : auto∶ Rˢ ≈⋯ Γₜ
    {Γ≈?} : auto∶ Γ″ ≈ᶜ Γ′
  R≈ = R≈? ¡; Γ≈ = Γ≈? ¡
  Γₜ″ = Cfgᵗ ∋ Γ″ at t′
  ∃Γ≈ = ∃ (_≈ᶜ Γ′) ∋ Γ″ , Γ≈
  𝕣   = ℝ∗⇒ℝ 𝕣∗
  open ℝ 𝕣 public
  𝕒 : 𝔸 Rˢ Γₜ″
  𝕒 = α , Γₜ , Γₜ′ , Γ→ , (refl , Γ≈) , R≈

  Rˢ′ : Run
  Rˢ′ = Γₜ″ ∷ Rˢ ⊣ 𝕒

  R≈′ : Rˢ′ ≈⋯ Γ′ at t′
  R≈′ = refl , Γ≈

  R = Rˢ; R′ = Rˢ′

auto-ℍ-Run : ∀ {Γₜ α Γₜ′} {Γ→ : Γₜ —[ α ]→ₜ Γₜ′} {Γ″} →
  {h : ℍ-Run? Γ→ Γ″} → ℍ-Run Γ→
auto-ℍ-Run {h = h} = record {ℍ-Run? h}

-- ** Stipulation: advertisting a contract
record H₁-args? Γ₀ : Type where
  constructor mk
  field
    {ad t} : _
  open ∣AD ad public
  field
    {vad?} : auto∶ ValidAd ad
    {hon?} : auto∶ Any (_∈ Hon) partG
    {d⊆?}  : auto∶ deposits ad ⊆′ deposits Γ₀
  vad = vad? ¡; hon = hon? ¡; d⊆ = (d⊆? ¡) .unmk⊆
  open Transition
    ( Γ₀ ⨾ t —— advertise⦅ ad ⦆ —→ ` ad ∣ Γ₀ ⨾ t
    ⊣ Act ([C-Advertise] vad hon d⊆)
    ) public hiding (t)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

mkℍ₁ : ∀ Γ₀ {A}{_ : H₁-args? Γ₀} → _ ⨾ _ ⨾ _ ~ℍ[1]~ _ ⨾ _
mkℍ₁ Γ₀ {A}{h} = mkℍ {record {Γ₀ = Γ₀; H₁-args? h}}{A}

-- ** Stipulation: committing secrets
record H₂-args?
  ad
  (Γ₀ : Cfg)
  (k⃗   : 𝕂²′ ad)
  (Δ×h̅ : List (Secret × Maybe ℕ × ℤ))
  : Type where
  constructor mk
  field {t A} : _
  open ∣AD ad public
    hiding (C)
  h̅  = List HashId             ∋ map (proj₂ ∘ proj₂) Δ×h̅
  Δ  = List (Secret × Maybe ℕ) ∋ map drop₃   Δ×h̅
  Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ
  as = unzip Δ .proj₁
  ms = unzip Δ .proj₂
  k̅  = concatMap (map pub ∘ codom) $ codom k⃗
  field
    {as≡?}  : auto∶ as ≡ secretsOfᵖ A G
    {All∉?} : auto∶ All (_∉ secretsOfᶜᶠ A Γ₀) as
    {Hon⇒?} : True (A ∈Hon⇒? ms)
  as≡ = as≡? ¡; All∉ = All∉? ¡; Hon⇒ = Hon⇒? ¡
  open Transition
    ( (` ad ∣ Γ₀) ⨾ t
    —— auth-commit⦅ A , ad , Δ ⦆ —→
      (` ad ∣ Γ₀ ∣ Δᶜ ∣ A auth[ ♯▷ ad ]) ⨾ t
    ⊣ Act ([C-AuthCommit] as≡ All∉ Hon⇒)
    ) public hiding (t)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₂ : ∀ ad Γ₀ (k⃗ : 𝕂²′ ad) Δ×h̅
  → {h? : H₂-args? ad Γ₀ k⃗ Δ×h̅}
  → H₂-args
auto-H₂ ad Γ₀ k⃗ Δ×h̅ {h?} =
  record {ad = ad; Γ₀ = Γ₀; k⃗ = k⃗; Δ×h̅ = Δ×h̅; H₂-args? h?}

mkℍ₂ : ∀ ad Γ₀ (k⃗ : 𝕂²′ ad) Δ×h̅ {h? : H₂-args? ad Γ₀ k⃗ Δ×h̅}{B : Participant} →
  let
    open H₂-args? h?
    C      = encodeAd ad (ad∈⇒Txout {ad}{Γ}{Rˢ} 𝟘 R≈ txout′)
    C,h̅,k̅  = encode (C , h̅ , k̅)
    C,h̅,k̅ₐ = SIG (K A) C,h̅,k̅
  in
  ∀ (∃B : ∃ λ B → (B →∗∶ C) ∈ toList Rᶜ)
  → All (λ l → ∀ X → l ≢ X →∗∶ C) (Any-tail $ ∃B .proj₂)
  → All (λ hᵢ → ∣ hᵢ ∣ᵐ ≡ η) h̅
  → All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)
  → CheckOracleInteractions Rᶜ Δ×h̅
  → {auto∶ Unique h̅}
  → {auto∶ Disjoint h̅ (codom sechash′)}
  → _ ⨾ _ ⨾ _ ~ℍ[2]~ _ ⨾ _
mkℍ₂ ad Γ₀ k⃗ Δ×h̅ {h?}{B} p₁ p₂ p₃ p₄ p₅ {p₆}{p₇} =
  mkℍ {auto-H₂ ad Γ₀ k⃗ Δ×h̅ {h?}}{B}
      p₁ p₂ p₃ p₄ p₅ (p₆ ¡) (p₇ ¡)

-- ** Stipulation: authorizing deposits
record H₃-args? (ad : Ad) (Γ₀ : Cfg) : Type where
  constructor mk
  field
    -- {ad Γ₀ t A x v} : _
    {x v} : _
    {t} : Time
    {A} : Participant
  open ∣AD ad public
  field
    {committedA?} : auto∶ partG ⊆ committedParticipants ad Γ₀
    {A∈per?}      : auto∶ (A , v , x) ∈ persistentDeposits G
  committedA = committedA? ¡; A∈per      = A∈per? ¡
  open Transition
    ( (` ad ∣ Γ₀) ⨾ t
    —— auth-init⦅ A , ad , x ⦆ —→
      (` ad ∣ Γ₀ ∣ A auth[ x ▷ˢ ad ]) ⨾ t
    ⊣ Act ([C-AuthInit] committedA A∈per)
    ) public hiding (t)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₃ : ∀ {ad Γ₀} {h? : H₃-args? ad Γ₀} → H₃-args
auto-H₃ {ad}{Γ₀}{h?} = record {ad = ad; Γ₀ = Γ₀; H₃-args? h?}

mkℍ₃ : ∀ ad Γ₀ {h? : H₃-args? ad Γ₀}(open H₃-args? h?){B : Participant} →
  let open H₃ (auto-H₃ {h? = h?}) using (T) in
  ∀ (∃B : ∃ λ B → B →∗∶ encode (T .proj₂ .proj₂) ∈ toList Rᶜ) →
  ∙ All (λ l → ∀ X → l ≢ X →∗∶ SIG (K̂ A) T) (Any-front $ ∃B .proj₂)
    ─────────────────────────────────────────────────────
    _ ⨾ _ ⨾ _ ~ℍ[3]~ _ ⨾ _
mkℍ₃ _ _ {h?}{B} p₁ p₂ =
  mkℍ {auto-H₃ {h? = h?}}{B} p₁ p₂

-- ** Stipulation: activating the contract
record H₄-args? : Type where
  constructor mk
  field
    {ad Γ₀ t z} : _
  open ∣AD ad public
  ds = persistentDeposits G
  vs = map select₂ ds
  xs = map select₃ ds
  v  = sum vs
  field
    {fresh-z?} : auto∶ z ∉ xs ++ ids Γ₀
  fresh-z = fresh-z? ¡
  Γ₁ = Cfg ∋ ` ad ∣ Γ₀
  Γ₂ = Cfg ∋ || map (λ{ (Aᵢ , vᵢ , xᵢ) →
    ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ  ad ] }) ds
  Γ₃ = Cfg ∋ || map (_auth[ ♯▷ ad ]) partG
  open Transition
    ( (Γ₁ ∣ Γ₂ ∣ Γ₃) ⨾ t
    —— init⦅ G , C ⦆ —→
      (⟨ C , v ⟩at z ∣ Γ₀) ⨾ t
    ⊣ Act ([C-Init] fresh-z)
    ) public hiding (t)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₄ : {h? : H₄-args?} → H₄-args
auto-H₄  {h?} = record {H₄-args? h?}

mkℍ₄ : ∀ {_ : H₄-args?} → _ ⨾ _ ⨾ _ ~ℍ[4]~ _ ⨾ _
mkℍ₄ {h?} = mkℍ {auto-H₄ {h?}}

-- ** Contract actions: authorize control
record H₅-args? : Type where
  constructor mk
  field
    {c v x Γ₀ t A} : _
    {i} : Index c
  open ∣SELECT c i public
  field
    {D≡A:D′?} : auto∶ A ∈ authDecorations d
  D≡A:D′ = D≡A:D′? ¡
  open Transition
    ( (⟨ c , v ⟩at x ∣ Γ₀) ⨾ t
      —— auth-control⦅ A , x ▷ d ⦆ —→
      (⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀) ⨾ t
    ⊣ Act ([C-AuthControl] D≡A:D′)
    ) public hiding (t)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₅ : {h? : H₅-args?} → H₅-args
auto-H₅  {h?} = record {H₅-args? h?}

mkℍ₅ : ∀ {_ : H₅-args?}{B : Participant} → _ ⨾ _ ⨾ _ ~ℍ[5]~ _ ⨾ _
mkℍ₅ {h?}{B} = mkℍ {auto-H₅ {h?}}{B}

-- ** Contract actions: put
record H₆-args? : Type where
  constructor mk
  field
    {c v y c′ y′ Γ₀ t p} : _
    {ds} : DepositRefs
    {ss} : List (Participant × Secret × ℕ)
    {i} : Index c
  vs = unzip₃ ds .proj₂ .proj₁
  xs = unzip₃ ds .proj₂ .proj₂ -- (i) xs = x₁⋯xₖ
  as = unzip₃ ss .proj₂ .proj₁
  Γ₁  = || map (uncurry₃ ⟨_has_⟩at_) ds
  Δ   = || map (uncurry₃ _∶_♯_) ss
  Γ₂  = Cfg ∋ Δ ∣ Γ₀
  Γ₁₂ = Cfg ∋ Γ₁ ∣ Γ₂
  open ∣SELECT c i public
  As = decorations d .proj₁
  ts = decorations d .proj₂
  field
    {t≡?} : auto∶ t ≡ maximum t ts
    {d≡?} : auto∶ d ≡⋯∶ put xs &reveal as if p ⇒ c′
    {fresh-y′?} : auto∶ y′ ∉ y L.∷ ids Γ₁₂
    {p⟦Δ⟧≡?} : auto∶ ⟦ p ⟧ᵖ Δ ≡ just true
    {As≡∅?} : auto∶ Null As
  t≡ = t≡? ¡; d≡ = d≡? ¡; fresh-y′ = fresh-y′? ¡; p⟦Δ⟧≡ = p⟦Δ⟧≡? ¡; As≡∅ = As≡∅? ¡
  Γ′ = ⟨ c′ , v + sum vs ⟩at y′ ∣ Γ₂
  private
    α  = put⦅ xs , as , y ⦆

    ∀≤t : All (_≤ t) ts
    ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

    put→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₁₂ —[ α ]→ Γ′
    put→ = ⟪ (λ ◆ → (⟨ [ ◆ ] , v ⟩at y ∣ (Γ₁ ∣ Γ₂) —[ α ]→ Γ′)) ⟫ d≡
           ~: [C-PutRev] {ds = ds} {ss = ss} fresh-y′ p⟦Δ⟧≡

  open Transition
    ( (⟨ c , v ⟩at y ∣ Γ₁₂) ⨾ t —— α —→ Γ′ ⨾ t
    ⊣ [Timeout] As≡∅ ∀≤t put→ refl
    ) public hiding (t; Γ′)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₆ : {h? : H₆-args?} → H₆-args
auto-H₆  {h?} = record {H₆-args? h?}

mkℍ₆ : ∀ {_ : H₆-args?} → _ ⨾ _ ⨾ _ ~ℍ[6]~ _ ⨾ _
mkℍ₆ {h?} = mkℍ {auto-H₆ {h?}}

-- ** Contract actions: authorize reveal
record H₇-args? : Type where
  constructor mk
  field
    {ad A a n Γ₀ t} : _
    {k⃗}   : 𝕂²′ ad
    {Δ×h̅} : List (Secret × Maybe ℕ × ℤ)
  open ∣AD ad public
  Δ = map drop₃   Δ×h̅
  h̅ = map select₃ Δ×h̅
  k̅ = concatMap (map pub ∘ codom) (codom k⃗)
  open Transition
    ( (⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀) ⨾ t —— auth-rev⦅ A , a ⦆ —→ A ∶ a ♯ n ∣ Γ₀ ⨾ t
    ⊣ Act [C-AuthRev]
    ) public hiding (t)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public
  field
    -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
    {∃α?} : auto∶ auth-commit⦅ A , ad , Δ ⦆ ∈ labelsʳ R
  ∃α = ∃α? ¡

auto-H₇ : {h? : H₇-args?} → H₇-args
auto-H₇  {h?} = record {H₇-args? h?}

-- mkℍ₇ : ∀ {h? : H₇-args?}{B : Participant}{mˢ : String}(let m = encode mˢ)
--   → let
--       open H₇-args? h? renaming (ad to ⟨G⟩C)

--       a∈R : a ∈ secrets Rˢ
--       a∈R = namesˡ⦅end⦆⊆ Rˢ
--           $ ∈namesˡ-resp-≈ a {Γ}{cfg (Rˢ .end)} (↭-sym $ R≈ .proj₂) 𝟘

--       open H₇ h using (txoutᶜ)
--     in
--   ∀ (∃λ : ∃ λ B → ∃ λ txoutᶜ →
--         let C,h̅,k̅ = encode (encodeAd ⟨G⟩C txoutᶜ , h̅ , k̅)
--         in  B →∗∶ SIG (K B) C,h̅,k̅ ∈ toList Rᶜ) →
--   ∀ { a ∈ secrets G
--   ∙ ∣ m ∣ᵐ ≥ η
--   ∙ (∃ λ B → (B , m , sechash′ {a} a∈R) ∈ oracleInteractionsᶜ Rᶜ)
--   ∙ All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃λ .proj₂ .proj₂)
--     ─────────────────────────────────────────────────────
--     _ ⨾ _ ⨾ _ ~ℍ[7]~ _ ⨾ _
-- mkℍ₇ {h?}{B}{m} p₁ p₂ =
--   mkℍ {auto-H₇ {h?}}{B}{m} p₁ p₂

-- ** Contract actions: split
record H₈-args? : Type where
  constructor mk
  field
    {c y Γ₀ t} : _
    {i} : Index c
    {vcis} : VIContracts
  open ∣SELECT c i public
  vs  = unzip₃ vcis .proj₁
  v   = sum vs
  cs  = unzip₃ vcis .proj₂ .proj₁
  vcs = zip vs cs
  xs  = unzip₃ vcis .proj₂ .proj₂
  As = decorations d .proj₁
  ts = decorations d .proj₂
  field
    {t≡?} : auto∶ t ≡ maximum t ts
    {d≡?} : auto∶ d ≡⋯∶ split vcs
    {fresh-xs?} : auto∶ All (_∉ y L.∷ ids Γ₀) xs
    {As≡∅?} : auto∶ Null As
  t≡ = t≡? ¡; d≡ = d≡? ¡; fresh-xs = fresh-xs? ¡; As≡∅ = As≡∅? ¡
  Γ₁ = || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis
  Γ′ = Γ₁ ∣ Γ₀
  private
    α  = split⦅ y ⦆

    ∀≤t : All (_≤ t) ts
    ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

    split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
    split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
          ~: [C-Split] {vcis = vcis} fresh-xs
  open Transition
    ( (⟨ c , v ⟩at y ∣ Γ₀) ⨾ t —— α —→ Γ′ ⨾ t
    ⊣ [Timeout] As≡∅ ∀≤t split→ refl
    ) public hiding (t; Γ′)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₈ : {H₈-args?} → H₈-args
auto-H₈  {h?} = record {H₈-args? h?}

mkℍ₈ : ∀ {H₈-args?} → _ ⨾ _ ⨾ _ ~ℍ[8]~ _ ⨾ _
mkℍ₈ {h?} = mkℍ {auto-H₈ {h?}}

-- ** Contract actions: withdraw
record H₉-args? : Type where
  constructor mk
  field
    {c v y Γ₀ A x t} : _
    {i} : Index c
  open ∣SELECT c i public
  As = decorations d .proj₁
  ts = decorations d .proj₂
  field
    {d≡?} : auto∶ d ≡⋯∶ withdraw A
    {fresh-x?} : auto∶ x ∉ y L.∷ ids Γ₀
    {As≡∅?} : auto∶ Null As
    {∀≤t?} : auto∶ All (_≤ t) ts
  d≡ = d≡? ¡; fresh-x = fresh-x? ¡; As≡∅ = As≡∅? ¡; ∀≤t = ∀≤t? ¡
  Γ′ = ⟨ A has v ⟩at x ∣ Γ₀
  private α  = withdraw⦅ A , v , y ⦆
  open Transition
    ( (⟨ c , v ⟩at y ∣ Γ₀) ⨾ t —— α —→ Γ′ ⨾ t
    ⊣ [Timeout] As≡∅ ∀≤t
        (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x)
        refl
    ) public hiding (t; Γ′)
  field {𝕙r?} : ℍ-Run? Γ→ Γ′
  𝕙r = auto-ℍ-Run {h = 𝕙r?}
  open ℍ-Run 𝕙r public

auto-H₉ : {H₉-args?} → H₉-args
auto-H₉  {h?} = record {H₉-args? h?}

mkℍ₉ : ∀ {H₉-args?} → _ ⨾ _ ⨾ _ ~ℍ[9]~ _ ⨾ _
mkℍ₉ {h?} = mkℍ {auto-H₉ {h?}}

-- -- ** Deposits: authorize join
-- record H₁₀-args : Type where
--   constructor mk
--   field
--     {A v x v′ x′ Γ₀ t} : _
--   open Transition
--     ( (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀) ⨾ t
--       —— auth-join⦅ A , x ↔ x′ ⦆ —→
--       ( ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′
--       ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀) ⨾ t
--     ⊣ Act [DEP-AuthJoin]
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: join
-- record H₁₁-args : Type where
--   constructor mk
--   field
--     {A v x v′ x′ y Γ₀ t} : _
--     -- Hypotheses from [DEP-Join]
--     fresh-y : y ∉ x L.∷ x′ ∷ ids Γ₀
--   open Transition
--     ( ( ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′
--       ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀) ⨾ t
--       —— join⦅ x ↔ x′ ⦆ —→
--       (⟨ A has (v + v′) ⟩at y ∣ Γ₀) ⨾ t
--     ⊣ Act ([DEP-Join] fresh-y)
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: authorize divide (similar to [10])
-- record H₁₂-args : Type where
--   constructor mk
--   field
--     {A v v′ x Γ₀ t} : _
--   open Transition
--     ( (⟨ A has (v + v′) ⟩at x ∣ Γ₀) ⨾ t
--       —— auth-divide⦅ A , x ▷ v , v′ ⦆ —→
--       (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀) ⨾ t
--     ⊣ Act [DEP-AuthDivide]
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: divide (similar to [11])
-- record H₁₃-args : Type where
--   constructor mk
--   field
--     {A v v′ x Γ₀ y y′ t} : _
--   field
--     -- Hypotheses from [DEP-Divide]
--     fresh-ys : All (_∉ x L.∷ ids Γ₀ ) [ y ⨾ y′ ]
--   open Transition
--     ( (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀) ⨾ t
--       —— divide⦅ x ▷ v , v′ ⦆ —→
--       (⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀) ⨾ t
--     ⊣ Act ([DEP-Divide] fresh-ys)
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: authorize donate (similar to [10])
-- record H₁₄-args : Type where
--   constructor mk
--   field
--     {A v x Γ₀ B′ t} : _
--   open Transition
--     ( (⟨ A has v ⟩at x ∣ Γ₀) ⨾ t
--       —— auth-donate⦅ A , x ▷ᵈ B′ ⦆ —→
--       (⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀) ⨾ t
--     ⊣ Act [DEP-AuthDonate]
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: donate (similar to [11])
-- record H₁₅-args : Type where
--   constructor mk
--   field
--     {A v x B′ Γ₀ y t} : _
--   field
--     -- Hypotheses from [DEP-Donate]
--     fresh-y : y ∉ x L.∷ ids Γ₀
--   open Transition
--     ( (⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀) ⨾ t
--       —— donate⦅ x ▷ᵈ B′ ⦆ —→
--       (⟨ B′ has v ⟩at y ∣ Γ₀) ⨾ t
--     ⊣ Act ([DEP-Donate] fresh-y)
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: authorize destroy
-- record H₁₆-args : Type where
--   constructor mk
--   field
--     {y Γ₀ t} : _
--     {ds} : DepositRefs
--     j : Index ds
--     -- Hypotheses from [DEP-AuthDestroy]
--     fresh-y : y ∉ ids Γ₀
--   k  = length ds
--   A  = (ds ‼ j) .proj₁
--   xs = map (proj₂ ∘ proj₂) ds
--   Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
--   j′ = Index xs ∋ ‼-map {xs = ds} j
--   open Transition
--     ( (Δ ∣ Γ₀) ⨾ t
--       —— auth-destroy⦅ A , xs , j′ ⦆ —→
--       (Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀) ⨾ t
--     ⊣ Act ([DEP-AuthDestroy] fresh-y)
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** Deposits: destroy
-- record H₁₇-args : Type where
--   constructor mk
--   field
--     {Γ₀ y t} : _
--     {ds} : DepositRefs
--     j : Index ds
--   xs = map (proj₂ ∘ proj₂) ds
--   Δ  = || flip map (enumerate ds) (λ{ (i , Aᵢ , vᵢ , xᵢ) →
--           ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
--   open Transition
--     ( (Δ ∣ Γ₀) ⨾ t
--       —— destroy⦅ xs ⦆ —→
--       Γ₀ ⨾ t
--     ⊣ Act [DEP-Destroy]
--     ) public hiding (t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public

-- -- ** After
-- record H₁₈-args : Type where
--   constructor mk
--   field
--     {Γ t δ} : _
--     δ>0 : δ > 0
--   open Transition
--     ( Γ ⨾ t —— delay⦅ δ ⦆ —→ Γ ⨾ (t + δ)
--     ⊣ [Delay] δ>0
--     ) public hiding (Γ; t)
--   field 𝕙r : ℍ-Run Γ→
--   open ℍ-Run 𝕙r public
