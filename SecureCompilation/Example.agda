----------------------------------------------------------------------------
-- Example contract compilations.
----------------------------------------------------------------------------
module SecureCompilation.Example where

open import Prelude.Init hiding (T)
open L.Mem
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Prelude.Validity
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Functor
open import Prelude.Lists.Collections
open import Prelude.Membership hiding (_∈_; _∉_; mapWith∈)
open import Prelude.ToList
open import Prelude.Traces
open import Prelude.InferenceRules
open import Prelude.Serializable

-- Bitcoin
module BTC where
  open import Bitcoin public
    using (_`=_; _`<_; _`∧_; `; `true; ∣_∣)
open import Bitcoin
  hiding ( t
         ; _`=_; _`<_; _`∧_; `; `true; ∣_∣
         )

-- BitML
open import BitML.Example.Setup using (Participant; Honest; A; B)
module BML where
  open import BitML Participant Honest public
    using (⟦_⟧_; _`=_; _`∧_; `_; `true; _`<_; _∣_)
open import BitML Participant Honest
  hiding ( t; a; v; A; B; x; y; x′; y′; Γ₀; Γₜ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′
         ; ∣_∣; `
         ; ⟦_⟧_; _`=_; _`∧_; `_; `true; _`<_; _∣_
         )

-- BitML compiler
η = 1024
open import SecureCompilation.Compiler Participant Honest η
open import SecureCompilation.ComputationalContracts Participant Honest

-- [TODO] move to `formal-bitcoin`
tx↝ : TxInput′ → TxInput
tx↝ record {tx′ = tx; index′ = i} = record {txId = tx ♯; index = toℕ i}

open import SymbolicModel.Run.Base Participant Honest as S
  hiding (Rˢ; Rˢ′)
open import SymbolicModel.Helpers Participant Honest
open import SymbolicModel.Mappings Participant Honest
open import SymbolicModel.Accessors Participant Honest

finPart : Finite Participant
finPart = 2 , Fun.mk↔
  {f   = λ where A → 0F; B → 1F}
  {f⁻¹ = λ where 0F → A; 1F → B}
  ((λ where 0F → refl; 1F → refl) , (λ where A → refl; B → refl))

postulate
  Kᵃ Kᵇ K̂ᵃ K̂ᵇ : KeyPair

keypairs : Participant → KeyPair × KeyPair
keypairs A = Kᵃ , K̂ᵃ
keypairs B = Kᵇ , K̂ᵇ

open import ComputationalModel.KeyPairs Participant keypairs
  renaming (K̂ to Kᵖʳⁱᵛ; K to Kᵖᵘᵇ)
open import ComputationalModel.Strategy Participant Honest finPart keypairs as C
  hiding (Rᶜ; Rᶜ′; λᶜ; m)
open import SecureCompilation.Helpers   Participant Honest finPart keypairs η
open import SecureCompilation.Coherence Participant Honest finPart keypairs η
-- open import SecureCompilation.DecidableCoherence Participant Honest finPart keypairs η

postulate
  encodeStr : String → Message
  decodeStr : Message → Maybe String

  reify-txout≡ : ∀ ad (txoutG txoutG′ : Txout ad) (txoutC txoutC′ : Txout (ad .C)) →
    ∙ txoutG ≗↦ txoutG′
    ∙ txoutC ≗↦ txoutC′
      ───────────────────────────────
      reify (ad , txoutG  , txoutC) ≡
      reify (ad , txoutG′ , txoutC′)

encode-txout≡ : ∀ ad (txoutG txoutG′ : Txout ad) (txoutC txoutC′ : Txout (ad .C)) →
  ∙ txoutG ≗↦ txoutG′
  ∙ txoutC ≗↦ txoutC′
    ────────────────────────────────
    encodeAd ad (txoutG  , txoutC) ≡
    encodeAd ad (txoutG′ , txoutC′)
encode-txout≡ ad txoutG txoutG′ txoutC txoutC′ txoutG≗ txoutC≗ =
  cong encodeMsg (reify-txout≡ ad txoutG txoutG′ txoutC txoutC′ txoutG≗ txoutC≗)

infix 0 _at0
_at0 : Cfg → Cfgᵗ
_at0 = _at 0

-- instance
--   Dec-Initial-Cfg : ∀ {Γ : Cfg} → Initial Γ ⁇
--   Dec-Initial-Cfg {Γ} .dec = go Γ
--     where
--       go : ∀ Γ → Dec (Initial Γ)
--       go ∅ᶜ                = yes tt
--       go (⟨ _ has _ ⟩at _) = yes tt
--       go (l ∣ r)           = Initial? l ×-dec Initial? r
--       go (⟨ _ , _ ⟩at _)   = no λ ()
--       go (l ∣ r)           = Initial? l ×-dec Initial? r
--       go _                 = no {!λ ()!}

--   Dec-Initial-Cfgᵗ : ∀ {Γₜ : Cfgᵗ} → Initial Γₜ ⁇
--   Dec-Initial-Cfgᵗ {Γ at t} .dec = Initial? Γ ×-dec (t ≟ 0)

infix 0 ∎_⊣_,_~_⊣_⊣_
∎_⊣_,_~_⊣_⊣_ :
  ∀ Γₜ₀ (init : Initial Γₜ₀) (ℽ₀ : ℾᵗ Γₜ₀) →
  ∀ (rᶜ : C.Run) (cinit : Initial rᶜ) →
  let open ℾᵗ ℽ₀; Γ₀ = Γₜ₀ .cfg in
  (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀) →
      let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in
      ∃ λ oᵢ → (txoutΓ (deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈) ≡ ∃T₀ at oᵢ)
            × (T₀ ‼ᵒ oᵢ ≡ v -redeemableWith- Kᵖʳⁱᵛ A))
  → (Γₜ₀ ∎⊣ init) ~ (rᶜ ∎⊣ cinit ✓)
∎ Γₜ ⊣ init , ℽ₀ ~ Rᶜ ⊣ cinit ⊣ txout≈ =
  -, base {ℽ = ℽ₀} init cinit txout≈

infixl -1 _—→ᴸ_⊣_~_⊣_ _—→ᴿ_⊣_~_⊣_ _—→ᵋ_⊣_
_—→ᴸ_⊣_~_⊣_ :
  ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
  ∀ Γₜ (λˢ : 𝕃 Rˢ Γₜ) λᶜ →
  (Γₜ ∷ Rˢ~Rᶜ .proj₁ ⊣ λˢ ✓) ~₁₁ (λᶜ ∷ Rᶜ ✓) →
  (Γₜ ∷ Rˢ ⊣ λˢ .proj₁) ~ (λᶜ ∷ Rᶜ ✓)
(𝕣∗ , coh) —→ᴸ Γₜ ⊣ λˢ ~ λᶜ ⊣ p =
  Γₜ ∷ 𝕣∗ ⊣ λˢ ✓ , step₁ {λˢ = λˢ} coh ([L] p)

_—→ᴿ_⊣_~_⊣_ :
  ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
  ∀ Γₜ (λˢ : 𝕃 Rˢ Γₜ) λᶜ →
  (Γₜ ∷ Rˢ~Rᶜ .proj₁ ⊣ λˢ ✓) ~₁₂ (λᶜ ∷ Rᶜ ✓) →
  (Γₜ ∷ Rˢ ⊣ λˢ .proj₁) ~ (λᶜ ∷ Rᶜ ✓)
(𝕣∗ , coh) —→ᴿ Γₜ ⊣ λˢ ~ λᶜ ⊣ p =
  Γₜ ∷ 𝕣∗ ⊣ λˢ ✓ , step₁ coh ([R] p)

_—→ᵋ_⊣_ :
  ∀ {Rˢ Rᶜ} (Rˢ~Rᶜ : Rˢ ~ Rᶜ) →
  ∀ λᶜ →
  Rˢ~Rᶜ .proj₁ ~₂ Rᶜ ∷ʳ λᶜ →
  Rˢ ~ (λᶜ ∷ Rᶜ ✓)
(𝕣∗ , coh) —→ᵋ λᶜ ⊣ p
  = 𝕣∗ , step₂ coh p

module Section7 where -- (see BitML paper, Section 7).

  x = "x"; y = "y"; x′ = "x′"; y′ = "y′"; x₁ = "x₁"

  ex-ad : Advertisement
  ex-ad = ⟨ A :! 1 at x ∣∣ B :! 1 at y ⟩ withdraw B ∙

  partG = nub-participants (ex-ad .G)

  postulate Kʷᵇ : Participant → KeyPair

  T₀ : Tx 0 2
  T₀ = record
    { inputs  = []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ (1 , record {value = 1 ; validator = ƛ (versig [ K̂ᵃ ] [ # 0 ])})
                ⨾ (1 , record {value = 1 ; validator = ƛ (versig [ K̂ᵇ ] [ # 0 ])})
                ]
    ; absLock = 0 }

  -- pre-existing deposits
  Tˣ Tʸ : TxInput′
  Tˣ = (-, -, T₀) at 0F
  Tʸ = (-, -, T₀) at 1F

  sechash : namesˡ (ex-ad .G) ↦ ℤ
  sechash ()

  txout : namesʳ (ex-ad .G) ↦ TxInput′
  txout = case_of λ where
    {- "x" -} 𝟘 → Tˣ
    {- "y" -} 𝟙 → Tʸ

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} 𝟘 → Kᵃ
    {- B -} 𝟙 → Kᵇ

  K² : subterms (ex-ad .C) ↦ (partG ↦ KeyPair)
  K² = case_of λ where
    𝟘 → case_of λ where
      {- A -} 𝟘 → Kʷᵇ A
      {- B -} 𝟙 → Kʷᵇ B

  Ks : List KeyPair
  Ks = mapWith∈ partG (K² $ here refl)

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs  = tx↝ <$> [ Tˣ ⨾ Tʸ ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 2 , record { value = 2; validator = ƛ versig Ks (allFin _) }]
    ; absLock = 0 }
  Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

  Tᵇ : Tx 1 1
  Tᵇ = sig⋆ [ Ks ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , record { value = 2; validator = ƛ versig [ K (there (here refl)) ] [ 0F ] }]
    ; absLock = 0 }

  out : ∃Tx¹ × (subterms⁺ ex-ad ↦′ ∃Txᶜ)
  out = bitml-compiler {ad = ex-ad} auto sechash txout K K²

  outTxs : Tx 2 1 × Tx 1 1
  outTxs = let t₀ , m = out in t₀ .proj₂ , m 𝟘 .proj₂

  _ = outTxs ≡ (Tᵢₙᵢₜ , Tᵇ)
    ∋ refl

  open BML

  Γ₀ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y

  ℽ₀ : ℾᵗ (Γ₀ at0)
  ℽ₀ = [txout: (λ where 𝟘 → Tˣ; 𝟙 → Tʸ) ∣sechash: (λ ()) ∣κ: (λ ()) ]

  rᶜ : C.Run
  rᶜ = [ submit (-, -, T₀)
       ⨾ (A →∗∶ [ Kᵖ A ⨾ K̂ᵖ A ])
       ⨾ (B →∗∶ [ Kᵖ B ⨾ K̂ᵖ B ])
       ]

  cinit : Initial rᶜ
  cinit = -, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl

  _ : _ ~ _
  _ =
    ∎   Γ₀ at0 ⊣ auto , ℽ₀
      ~ rᶜ     ⊣ cinit
      ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

    —→ᴸ (` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y) at 0
        ⊣ ((advertise⦅ ex-ad ⦆ , _) , _)
      ~ (A →∗∶ _) -- encode tx txout
      ⊣ [1] {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y}
            auto (_ , auto) auto auto (toWitness {Q = _ ⊆? _} tt)
      -- ⊣ [1]⋯ {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y} _

    -- —→ᴸ (` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
    --              ∣ A auth[ ♯▷ ex-ad ]) at 0
    --              ⊣ ((auth-commit⦅ A , ex-ad , [] ⦆ , _) , _)
    --   ~ (A →∗∶ _)
    --   ⊣ [2] {k⃗ = K²} auto (_ , auto) auto auto auto
    --         ? ? [] ? [] auto (λ ())

    -- —→ᴸ (` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
    --              ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]) at 0
    --              ⊣ ((auth-commit⦅ B , ex-ad , [] ⦆ , _) , _)
    --   ~ (B →∗∶ _)
    --   ⊣ [2] {k⃗ = K²} auto (_ , auto) auto auto auto
    --         ? ? [] ? [] auto (λ ())

    -- —→ᴸ (` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    --           ∣ ⟨ A ∶ a ♯ just 9 ⟩
    --           ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]
    --           | A auth[ x ▷ˢ ex-ad ]) at 0
    --           ⊣ ((auth-init⦅ A , ex-ad , x ⦆ , _) , _)
    --   ~ (A →∗∶ _)
    --   ⊣ [3] auto (_ , auto) ? 𝟘 ? ?

    -- —→ᴸ (` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
    --           ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]
    --           | A auth[ x ▷ˢ ex-ad ] | B auth[ y ▷ˢ ex-ad ]) at 0
    --           ⊣ ((auth-init⦅ B , ex-ad , y ⦆ , _) , _)
    --   ~ (B →∗∶ _)
    --   ⊣ [L] [3] auto (_ , auto) ? 𝟙 ? ?

    -- —→ᴸ (⟨ ex-ad .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩) at 0
    --     ⊣ ((init⦅ ex-ad .G , ex-ad .C ⦆ , _) , _)
    --   ~ submit (-, -, Tᵢₙᵢₜ)
    --   ⊣ [L] [4] auto (_ , auto) auto)

    -- —→ᴸ (⟨ ex-ad .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9) at 0
    --     ⊣ ((auth-rev⦅ A , a ⦆ , _) , _)
    --   ~ (A →∗∶ encodeStr a)
    --   ⊣ [L] [7] ? auto (_ , auto) (A , ?) ? ? ? ?)

    -- —→ᴸ (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9) at 0
    --     ⊣ ((put⦅ [] , [ a ] , x₁ ⦆ , _) , _)
    --   ~ submit (-, -, T′)
    --   ⊣ [L] [6] refl refl auto (_ , auto) auto ? refl)

  module M₀ where
    Γₜ = Γ₀ at0
    Rˢ = Γₜ ∎⊣ auto

    Rᶜ : CRun
    Rᶜ = rᶜ ∎⊣ cinit ✓

    coh : Rˢ ~ Rᶜ
    coh = -, base {ℽ = ℽ₀} auto cinit
      λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl
    𝕣∗ = coh .proj₁

  module M₁ where
    open M₀ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = advertise⦅ ex-ad ⦆
    Γ  = ` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
    Γₜ = Γ at0
    Rˢ = Γₜ ⟨ Act {t = 0} $ C-Advertise {ad = ex-ad} {Γ = Γ₀} ⟩←—— Rˢ′

    d⊆ : ex-ad ⊆⦅ deposits ⦆ Γ₀
    d⊆ = toWitness {Q = _ ⊆? _} tt

    vad = Valid ex-ad ∋ auto
    txoutΓ = Txout Γ ∋ Txout≈ {Rˢ′ ∙cfg}{Γ₀} auto (𝕣 ∙txoutEnd_)
    txoutG = Txout ex-ad ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {ex-ad}{Γ₀} d⊆)
    txoutC = Txout (ex-ad .C) ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad .names-⊆)

    _C = encodeAd ex-ad (txoutG , txoutC)
    λᶜ = A →∗∶ _C
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [1] auto (Γ , auto) auto auto d⊆)
    𝕣∗ = coh .proj₁

  module M₂ where
    open M₁ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-commit⦅ A , ex-ad , [] ⦆
    Γ  = ` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                 ∣ A auth[ ♯▷ ex-ad ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y} {secrets = []}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    txoutGC = ad∈⇒Txout {ex-ad}{M₁.Γ}{Rˢ′}{0} (here refl) auto txout′
    txoutG = txoutGC .proj₁; txoutC = txoutGC .proj₂
    _C = encodeAd ex-ad txoutGC

    C≡ : _C ≡ M₁._C
    C≡ = encode-txout≡ ex-ad txoutG M₁.txoutG txoutC M₁.txoutC
           (λ where 𝟘 → refl; 𝟙 → refl) λ ()

    h̅ : List ℤ
    h̅ = []

    k⃗ : 𝕂²′ ex-ad
    k⃗ = K²

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ = _C ◇ h̅ ◇ k̅
    C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ A) C,h̅,k̅

    λᶜ = A →∗∶ C,h̅,k̅ₐ
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂)
      ([L] [2] {k⃗ = k⃗} auto (_ , auto) auto auto auto ∃B first-∃B [] first-λᶜ [] auto h♯sechash)
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite C≡ = A , 𝟘

        postulate
          first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ _C) (Any-tail $ ∃B .proj₂)
          first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)

        h♯sechash : Disjoint h̅ (codom sechash′)
        h♯sechash (() , _)
    𝕣∗ = coh .proj₁

  module M₃ where
    open M₂ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-commit⦅ B , ex-ad , [] ⦆
    Γ  = ` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                 ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y ∣ A auth[ ♯▷ ex-ad ]}
                      {secrets = []}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    txoutGC = ad∈⇒Txout {ex-ad}{M₂.Γ}{Rˢ′}{0} (here refl) auto txout′
    txoutG = txoutGC .proj₁; txoutC = txoutGC .proj₂
    _C = encodeAd ex-ad txoutGC

    C≡ : _C ≡ M₁._C
    C≡ = encode-txout≡ ex-ad txoutG M₁.txoutG txoutC M₁.txoutC
           (λ where 𝟘 → refl; 𝟙 → refl) λ ()

    h̅ : List ℤ
    h̅ = []

    k⃗ : 𝕂²′ ex-ad
    k⃗ = K²

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ = encode (_C , h̅ , k̅)
    C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ B) C,h̅,k̅

    λᶜ = B →∗∶ C,h̅,k̅ₐ
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂)
      ([L] [2] {k⃗ = k⃗} auto (_ , auto) auto auto auto ∃B first-∃B [] first-λᶜ [] auto λ ())
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite C≡ = A , 𝟙

        postulate
          first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ _C) (Any-tail $ ∃B .proj₂)
          first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)
    𝕣∗ = coh .proj₁
{-
  module M₄ where
    open M₃ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-init⦅ A , ex-ad , x ⦆
    Γ  = ` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                 ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]
                 ∣ A auth[ x ▷ˢ ex-ad ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                       ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]} {v = 1}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants ex-ad
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
        ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 ex-ad (⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                       ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ])
                       A x auto Γ→ (Γ , auto) committedA
      public using (T; λˢ)

    m  = [ SIG (Kᵖʳⁱᵛ A) T ]
    λᶜ = A →∗∶ m
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA 𝟘 ∃B first-∃B)
      where
        postulate
          ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
          first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃B .proj₂)
    𝕣∗ = coh .proj₁

  module M₅ where
    open M₄ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-init⦅ B , ex-ad , y ⦆
    Γ  = ` ex-ad ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                 ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]
                 ∣ A auth[ x ▷ˢ ex-ad ] ∣ B auth[ y ▷ˢ ex-ad ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                       ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ]
                       ∣ A auth[ x ▷ˢ ex-ad ]} {v = 1}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants ex-ad
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
        ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 ex-ad (⟨ A has 1 ⟩at x ∣ ⟨ B has 1 ⟩at y
                       ∣ A auth[ ♯▷ ex-ad ] ∣ B auth[ ♯▷ ex-ad ] ∣ A auth[ x ▷ˢ ex-ad ])
                       B y auto Γ→ (Γ , auto) committedA
      public using (T)

    m  = [ SIG (Kᵖʳⁱᵛ B) T ]
    λᶜ = B →∗∶ m
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA 𝟙 ∃B first-∃B)
      where
        postulate
          ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
          first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-front $ ∃B .proj₂)
    𝕣∗ = coh .proj₁

  module M₆ where
    open M₅ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = init⦅ ex-ad .G , ex-ad .C ⦆
    Γ  = ⟨ ex-ad .C , 2 ⟩at x₁
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-Init {x = x₁} {Γ = ∅ᶜ}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    toSpend = persistentDeposits (ex-ad .G)

    open H₄ 𝕣 0 α 0 ex-ad _ toSpend 2 x₁ auto Γ→ (Γ , auto)
      public using (T; λˢ)

    λᶜ = submit T
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    -- 𝕣∗ : ℝ∗ Rˢ
    -- 𝕣∗ = Γₜ ∷ 𝕣∗′ ⊣ λˢ ✓

    -- coh₁₁ : 𝕣∗ ~₁₁ Rᶜ
    -- coh₁₁ = [4] {ex-ad}{∅ᶜ}{0}{x₁}{Rᶜ′}{Rˢ′}{𝕣∗′} auto (Γ , auto) λ where 𝟘⊥; 𝟙⊥

    -- coh₁ : 𝕣∗ ~₁ Rᶜ
    -- coh₁ = [L] coh₁₁

    -- coh∗ : 𝕣∗ ~′ Rᶜ
    -- coh∗ = step₁ (coh′ .proj₂) coh₁

    coh : Rˢ ~ Rᶜ
    -- coh = -, coh∗
    coh = -, step₁ (coh′ .proj₂)
      ([L] [4] {ex-ad}{∅ᶜ}{0}{x₁}{Rᶜ′}{Rˢ′}{𝕣∗′} auto (Γ , auto) λ where 𝟘⊥; 𝟙⊥)
    𝕣∗ = coh .proj₁
-}

{-
  module M₇ where
    open M₆ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-rev⦅ A , a ⦆
    Γ  = ⟨ ex-ad .C , 1 ⟩at x₁
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ [C-AuthRev] {n = 9} {Γ = ⟨ ex-ad .C , 1 ⟩at x₁}
    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ = A →∗∶ encodeStr a
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [7] ? auto (Γ , auto) (A , ?) ? ? ? ?)
    -- coh = -, step₁ (coh′ .proj₂) ([L] [7] ? auto (Γ , auto) (A , 𝟘) 𝟜 𝟘 ? ?)
    𝕣∗ = coh .proj₁

  module M₈ where
    open M₇ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = put⦅ [] , [ a ] , x₁ ⦆
    Γ  = ⟨ [ withdraw A ] , 1 ⟩at x₂
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Timeout {c = ex-ad .C} {t = 0} {v = 1} {i = 0F}
       $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = submit T′

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [6] refl refl auto (Γ , auto) auto ? refl)

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

  module M₉ where
    open M₈ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = withdraw⦅ A , 1 , x₂ ⦆
    Γ  = ⟨ [ withdraw A ] , 1 ⟩at x₂
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Timeout {c = [ withdraw A ]} {t = 0} {v = 1} {i = 0F}
       $ C-Withdraw {x = x₃} {Γ = ∅ᶜ}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = submit T′ᵃ

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [9] refl auto (Γ , auto) auto refl [])

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁
-}

{-
module TimedCommitment where -- (see BitML, Appendix A.5)

  open import BitML.Example.TimedCommitment

  -- t = 42 ;
  v = 1 ; Ha = + 9

  partG = nub-participants (tc .G)

  postulate Kᵈ¹ Kᵈ² Kʷᵃ : Participant → KeyPair

  T₀ : Tx 0 2
  T₀ = record
    { inputs  = []
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ (1 , record {value = 1 ; validator = ƛ (versig [ K̂ᵃ ] [ # 0 ])})
                ⨾ (1 , record {value = 0 ; validator = ƛ (versig [ K̂ᵇ ] [ # 0 ])})
                ]
    ; absLock = 0 }

  -- pre-existing deposits
  Tᵃ Tᵇ : TxInput′
  Tᵃ = (-, -, T₀) at 0F
  Tᵇ = (-, -, T₀) at 1F

  sechash : namesˡ (tc .G) ↦ ℤ
  sechash = case_of λ where
    {- "a" -} 𝟘 → Ha

  txout : namesʳ (tc .G) ↦ TxInput′
  txout = case_of λ where
    {- "x" -} 𝟘 → Tᵃ
    {- "y" -} 𝟙 → Tᵇ

  K : partG ↦ KeyPair
  K = case_of λ where
    {- A -} 𝟘 → Kᵃ
    {- B -} 𝟙 → Kᵇ

  K² : subterms (tc .C) ↦ (partG ↦ KeyPair)
  K² = case_of λ where
    {- reveal "a" ⇒ withdraw A -}
    𝟘 → case_of λ where
      {- A -} 𝟘 → Kᵈ² A
      {- B -} 𝟙 → Kᵈ² B
    {- withdraw A -}
    𝟙 → case_of λ where
      {- A -} 𝟘 → Kʷᵃ A
      {- B -} 𝟙 → Kʷᵃ B
    {- after t ⇒ withdraw B -}
    𝟚 → case_of λ where
      {- A -} 𝟘 → Kᵈ² A
      {- B -} 𝟙 → Kᵈ² B

  K⋆ : subterms (tc .C) ↦ List KeyPair
  K⋆ = mapWith∈ partG ∘ K²

  module _ where
    open BTC

    e₁ : Script 3 `Bool
    e₁ = versig (K⋆ 𝟘) ⟦ # 0 , # 1 ⟧
      `∧ `true
      `∧ ⋀ [ hash (var (# 2)) `= ` (sechash 𝟘) `∧ (` (+ η) `< ∣ var (# 2) ∣) ]

    e₂ : Script 3 `Bool
    e₂ = versig (K⋆ 𝟚) ⟦ # 0 , # 1 ⟧

    e′ : Script 2 `Bool
    e′ = versig (K⋆ 𝟙) ⟦ # 0 , # 1 ⟧

  Tᵢₙᵢₜ : Tx 2 1
  Tᵢₙᵢₜ = record
    { inputs  = tx↝ <$> [ Tᵃ ⨾ Tᵇ ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ _ , record { value = v ; validator = ƛ (e₁ `∨ e₂) }]
    ; absLock = 0 }
  Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

  T′ : Tx 1 1
  T′ = sig⋆ [ K⋆ 𝟘 ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ _ , record { value = v ; validator = ƛ e′ }]
    ; absLock = 0 }

  T′ᵃ : Tx 1 1
  T′ᵃ = sig⋆ [ K⋆ 𝟙 ] record
    { inputs  = [ ((∃Tx ∋ -, -, T′) ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , record { value = v ; validator = ƛ versig [ K 𝟘 ] [ # 0 ] }]
    ; absLock = 0 }

  T′ᵇ : Tx 1 1
  T′ᵇ = sig⋆ [ K⋆ 𝟚 ] record
    { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
    ; wit     = wit⊥
    ; relLock = V.replicate 0
    ; outputs = [ 1 , record { value = v ; validator = ƛ versig [ K 𝟙 ] [ # 0 ] }]
    ; absLock = t }

  out : ∃Tx¹ × (subterms⁺ tc ↦′ ∃Txᶜ)
  out = bitml-compiler {ad = tc} auto sechash txout K K²

  outTxs : Tx 2 1 × Tx 1 1 × Tx 1 1 × Tx 1 1
  outTxs = let t₀ , m = out in
      t₀ .proj₂
    , m 𝟘 .proj₂
    , m 𝟙 .proj₂
    , m 𝟚 .proj₂

  _ = outTxs ≡ (Tᵢₙᵢₜ , T′ , T′ᵃ , T′ᵇ)
    ∋ refl

  --

  Γ₀ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  Γₙ = ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N

  tc-run : S.Run
  tc-run = record {start = Γ₀ at0; init = auto; end = Γₙ at0; trace = -, tc-stepsₜ}

  h : ℤ
  h = a ♯
  ℽ₀ : ℾᵗ (Γ₀ at0)
  ℽ₀ = [txout: (λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ) ∣sechash: (λ ()) ∣κ: (λ ()) ]

  rᶜ : C.Run
  rᶜ = [ submit (-, -, T₀)
       ⨾ (A →∗∶ [ Kᵖ A ⨾ K̂ᵖ A ])
       ⨾ (B →∗∶ [ Kᵖ B ⨾ K̂ᵖ B ])
       ]

  cinit : Initial rᶜ
  cinit = -, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl

  _ : _ ~ _
  _ =
    ∎   Γ₀ at0 ⊣ auto , ℽ₀
      ~ rᶜ     ⊣ cinit
      ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

    —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
              ⊣ ((advertise⦅ tc ⦆ , _) , _)
      ~ (A →∗∶ _) -- encode tx txout
      ⊣ [1] {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y}
            auto (_ , auto) auto auto (toWitness {Q = _ ⊆? _} tt)

    —→ᵋ (A →O∶ encodeStr a)
      ⊣ [2] (inj₁ refl)

    —→ᵋ (O→ A ∶ [ h ])
      ⊣ [2] (inj₂ refl)

    -- —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    --           ∣ ⟨ A ∶ a ♯ just 9 ⟩
    --           ∣ A auth[ ♯▷ tc ]) at 0
    --           ⊣ ((auth-commit⦅ A , tc , [ a , just N ] ⦆ , _) , _)
    --   ~ (A →∗∶ _)
    --   ⊣ [2] {k⃗ = K²} auto (_ , auto) auto auto auto
    --          {!!} ? ({!!} ∷ []) ? ((A , encodeStr a , 𝟘 , {!!}) ∷ [])
    --          auto (λ where (𝟘 , ()))

    -- —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    --           ∣ ⟨ A ∶ a ♯ just 9 ⟩
    --           ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]) at 0
    --           ⊣ ((auth-commit⦅ B , tc , [] ⦆ , _) , _)
    --   ~ (B →∗∶ _)
    --   ⊣ [2] {k⃗ = K²} auto (_ , auto) auto auto auto
    --         ? ? [] ? [] auto (λ ())

    -- —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    --           ∣ ⟨ A ∶ a ♯ just 9 ⟩
    --           ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
    --           | A auth[ x ▷ˢ tc ]) at 0
    --           ⊣ ((auth-init⦅ A , tc , x ⦆ , _) , _)
    --   ~ (A →∗∶ _)
    --   ⊣ [3] auto (_ , auto) ? 𝟘 ? ?

    -- —→ᴸ (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
    --           ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
    --           | A auth[ x ▷ˢ tc ] | B auth[ y ▷ˢ tc ]) at 0
    --           ⊣ ((auth-init⦅ B , tc , y ⦆ , _) , _)
    --   ~ (B →∗∶ _)
    --   ⊣ [L] [3] auto (_ , auto) ? 𝟙 ? ?

    -- —→ᴸ (⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩) at 0
    --     ⊣ ((init⦅ tc .G , tc .C ⦆ , _) , _)
    --   ~ submit (-, -, Tᵢₙᵢₜ)
    --   ⊣ [L] [4] auto (_ , auto) auto)

    -- —→ᴸ (⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9) at 0
    --     ⊣ ((auth-rev⦅ A , a ⦆ , _) , _)
    --   ~ (A →∗∶ encodeStr a)
    --   ⊣ [L] [7] ? auto (_ , auto) (A , ?) ? ? ? ?)

    -- —→ᴸ (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9) at 0
    --     ⊣ ((put⦅ [] , [ a ] , x₁ ⦆ , _) , _)
    --   ~ submit (-, -, T′)
    --   ⊣ [L] [6] refl refl auto (_ , auto) auto ? refl)

    -- —→ᴸ (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
    --     ⊣ ((withdraw⦅ A , 1 , ₂ ⦆ , _) , _)
    --   ~ submit (-, -, T′ᵃ)
    --   ⊣ [L] [9] refl auto (_ , auto) auto refl []

{-
    (
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
            ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]} {v = 0}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
            ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
            ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                      ∣ A auth[ ♯▷ tc ]} {secrets = []}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]) at 0
    ⟨ Act {t = 0}
    $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]}
    ⟩←——
      (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    ⟨ Act {t = 0}
    $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y}
    ⟩←——
      Γ₀ at0
    ∎⊣ auto
    )
    ~
    ( (B →∗∶ _)
    ∷ (A →∗∶ _)
    ∷ (O→ A ∶ _)
    ∷ (A →O∶ _)
    ∷ (A →∗∶ _)
    ∷ [ submit (-, -, T₀)
      ⨾ (A →∗∶ [ Kᵖ A ⨾ K̂ᵖ A ])
      ⨾ (B →∗∶ [ Kᵖ B ⨾ K̂ᵖ B ])
      ] ∎⊣ (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
    ✓ ✓ ✓ ✓ ✓ ✓
    )
-}

{-
  -, -, step₁ (step₁ (step₁ (step₁ (step₁ (step₁ (step₁ (step₁ (step₂ (step₂
                    (base {ℽ = ℽ₀} auto cinit
                      λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)
                    ([2] (inj₁ refl)))
                  ([2] (inj₂ refl)))
                ([L] [2] {k⃗ = K²} auto (_ , auto) auto auto auto ?
                          (? ∷ []) ((A , encodeStr a , 𝟘 , {!!}) ∷ []) auto (λ where (𝟘 , ()))))
              ([L] [2] {k⃗ = K²} auto (_ , auto) auto auto auto ? [] [] auto λ ()))
            ([L] [3] auto (_ , auto) ? 𝟘 ?))
          ([L] [3] auto (_ , auto) ? auto ?))
        ([L] [4] auto (_ , auto) auto))
      ([L] [7] ? auto (_ , auto) (A , ?) ? ? ? ?))
    ([L] [6] refl refl auto (_ , auto) auto ? refl))
  ([L] [9] refl auto (_ , auto) auto refl [])
-}
{-
  module M₀ where
    Γₜ = Γ₀ at0
    Rˢ = Γₜ ∎⊣ auto

    Rᶜ : CRun
    Rᶜ = rᶜ ∎⊣ cinit ✓

    coh : Rˢ ~ Rᶜ
    coh = -, base {ℽ = ℽ₀} auto cinit
      λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl
    𝕣∗ = coh .proj₁

  module M₁ where
    open M₀ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = advertise⦅ tc ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    Γₜ = Γ at0
    Rˢ = Γₜ ⟨ Act {t = 0} $ C-Advertise {ad = tc} {Γ = Γ₀} ⟩←—— Rˢ′

    d⊆ : tc ⊆⦅ deposits ⦆ Γ₀
    d⊆ = toWitness {Q = _ ⊆? _} tt

    txoutΓ = Txout Γ ∋ Txout≈ {Rˢ′ ∙cfg}{Γ₀} auto (𝕣 ∙txoutEnd_)
    txoutG = Txout tc ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {tc}{Γ₀} d⊆)

    _ : txoutG ≗↦ txout
    _ = λ where 𝟘 → refl; 𝟙 → refl

    _C = encode tc txoutG
    λᶜ = A →∗∶ _C
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [1] auto (Γ , auto) auto auto d⊆)
    𝕣∗ = coh .proj₁

  module M₁′ where
    open M₁ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    Rˢ = Rˢ′
    λᶜ = A →O∶ encodeStr a
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = let _ , coh₁ = coh′
          in -, step₂ coh₁ ([2] (inj₁ refl))
    𝕣∗ = coh .proj₁

  module M₁″ where
    open M₁′ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    Rˢ = Rˢ′
    λᶜ = O→ A ∶ [ h ]
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = let _ , coh₁ = M₁′.coh
          in -, step₂ coh₁ ([2] (inj₂ refl))
    𝕣∗ = coh .proj₁

  module M₂ where
    open M₁″ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-commit⦅ A , tc , [ a , just N ] ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
              ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    txoutG : Txout tc
    txoutG = ad∈⇒TxoutG {tc}{M₁.Γ}{Rˢ′}{0} (here refl) auto txout′

    _C = encode tc txoutG

    C≡ : _C ≡ M₁._C
    C≡ = ? -- encode-txout≡ tc txoutG M₁.txoutG λ where 𝟘 → refl; 𝟙 → refl

    h̅ : List ℤ
    h̅ = [ h ]

    k⃗ : 𝕂²′ tc
    k⃗ = K²

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)
    -- ≈ pub <$> [Kᵈ² A, Kᵈ² B, Kʷᵃ A, Kʷᵃ B, Kᵈ² A, Kᵈ² B]

    C,h̅,k̅ = encode (_C , h̅ , k̅)
    C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ A) C,h̅,k̅

    λᶜ = A →∗∶ C,h̅,k̅ₐ
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂)
      ([L] [2] {k⃗ = k⃗} auto (_ , auto) auto auto auto ∃B first-∃B h≡ first-λᶜ h∈O auto h♯sechash)
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite C≡ = A , 𝟚

        first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ _C) (Any-tail $ ∃B .proj₂)
        first-∃B = {!!}

        h≡ : All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅
        h≡ = {!!} ∷ []

        first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)
        first-λᶜ = {!!}

        h∈O : CheckOracleInteractions Rᶜ′ _
        h∈O = (A , encodeStr a , 𝟘 , {!!}) ∷ []

        h♯sechash : Disjoint h̅ (codom sechash′)
        h♯sechash (𝟘 , ())
    𝕣∗ = coh .proj₁

  module M₃ where
    open M₂ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-commit⦅ B , tc , [] ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
              ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]}
                      {secrets = []}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    txoutG : Txout tc
    txoutG = ad∈⇒TxoutG {tc}{M₂.Γ}{Rˢ′}{0} (here refl) auto txout′

    _C = encode tc txoutG

    C≡ : _C ≡ M₁._C
    C≡ = ? -- encode-txout≡ tc txoutG M₁.txoutG λ where 𝟘 → refl; 𝟙 → refl

    h̅ : List ℤ
    h̅ = []

    k⃗ : 𝕂²′ tc
    k⃗ = K²

    k̅ : List ℤ
    k̅ = concatMap (map pub ∘ codom) (codom k⃗)

    C,h̅,k̅ = encode (_C , h̅ , k̅)
    C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ B) C,h̅,k̅

    λᶜ = B →∗∶ C,h̅,k̅ₐ
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂)
      ([L] [2] {k⃗ = k⃗} auto (_ , auto) auto auto auto ∃B first-∃B [] first-λᶜ [] auto λ ())
      where
        ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList Rᶜ′
        ∃B rewrite C≡ = A , 𝟛

        first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ _C) (Any-tail $ ∃B .proj₂)
        first-∃B = {!!}

        first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)
        first-λᶜ = {!!}
    𝕣∗ = coh .proj₁

  module M₄ where
    open M₃ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-init⦅ A , tc , x ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
              ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
              ∣ A auth[ x ▷ˢ tc ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants tc
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
        ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 tc (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
                       A x auto Γ→ (Γ , auto) committedA
      public using (T; λˢ)

    m  = [ SIG (Kᵖʳⁱᵛ A) T ]
    λᶜ = A →∗∶ m
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA 𝟘 ∃B first-∃B)
      where
        ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
        ∃B = {!!}

        first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail $ ∃B .proj₂)
        first-∃B = {!!}
    𝕣∗ = coh .proj₁

  module M₅ where
    open M₄ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-init⦅ B , tc , y ⦆
    Γ  = ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
              ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
              ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]} {v = 0}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    committedA : partG ⊆ committedParticipants tc
        ( ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
        ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ])
    committedA = toWitness {Q = _ ⊆? _} tt

    open H₃ 𝕣 0 α 0 tc (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ])
                       B y auto Γ→ (Γ , auto) committedA
      public using (T)

    m  = [ SIG (Kᵖʳⁱᵛ B) T ]
    λᶜ = B →∗∶ m
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [3] auto (Γ , auto) committedA auto ∃B first-∃B)
      where
        ∃B : ∃ λ B → (B →∗∶ [ T ♯ ]) ∈ toList Rᶜ′
        ∃B = {!!}

        first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail $ ∃B .proj₂)
        first-∃B = {!!}
    𝕣∗ = coh .proj₁
-}

{-
  module M₆ where
    open M₅ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = init⦅ tc .G , tc .C ⦆
    Γ  = ⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩}
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    toSpend = persistentDeposits (tc .G)

    open H₄ 𝕣 0 α 0 tc (⟨ A ∶ a ♯ just 9 ⟩) toSpend 1 x₁ auto Γ→ (Γ , auto)
      public using (T)

    λᶜ = submit T
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [4] auto (Γ , auto) auto)
    𝕣∗ = coh .proj₁
-}

{-
  module M₇ where
    open M₆ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = auth-rev⦅ A , a ⦆
    Γ  = ⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
    Γₜ = Γ at0
    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Act {t = 0}
       $ [C-AuthRev] {n = 9} {Γ = ⟨ tc .C , 1 ⟩at x₁}
    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ = A →∗∶ encodeStr a
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [7] ? auto (Γ , auto) (A , ?) ? ? ? ?)
    -- coh = -, step₁ (coh′ .proj₂) ([L] [7] ? auto (Γ , auto) (A , 𝟘) 𝟜 𝟘 ? ?)
    𝕣∗ = coh .proj₁
-}

{-
  module M₈ where
    open M₇ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = put⦅ [] , [ a ] , x₁ ⦆
    Γ  = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Timeout {c = tc .C} {t = 0} {v = 1} {i = 0F}
       $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = submit T′

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [6] refl refl auto (Γ , auto) auto ? refl)

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁

  module M₉ where
    open M₈ using () renaming (Rˢ to Rˢ′; 𝕣∗ to 𝕣∗′; Rᶜ to Rᶜ′; coh to coh′)
    𝕣 = ℝ∗⇒ℝ 𝕣∗′
    open ℝ 𝕣 public

    α  = withdraw⦅ A , 1 , x₂ ⦆
    Γ  = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
    Γₜ = Γ at0

    Γ→ : _ —[ α ]→ₜ _
    Γ→ = Timeout {c = [ withdraw A ]} {t = 0} {v = 1} {i = 0F}
       $ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9}

    Rˢ : S.Run
    Rˢ = Γₜ ⟨ Γ→ ⟩←—— Rˢ′

    λᶜ : C.Label
    λᶜ = submit T′ᵃ

    Rᶜ : CRun
    Rᶜ = λᶜ ∷ Rᶜ′ ✓

    coh : Rˢ ~ Rᶜ
    coh = -, step₁ (coh′ .proj₂) ([L] [9] refl auto (Γ , auto) auto refl [])

    𝕣∗ : ℝ∗ Rˢ
    𝕣∗ = coh .proj₁
-}
-}
