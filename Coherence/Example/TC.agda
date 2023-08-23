module Coherence.Example.TC where

import Bitcoin as BTC
open import Coherence.Example.Setup
open import SymbolicModel ⋯′ as S
  hiding ( C; G; t; a; v; A; B; x; y; Γ₀; Γₜ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′; Γ″
          ; _`=_; _`∧_; _`∨_; `true; _`<_
          ; Rˢ; Rˢ′; Σ
          )
open import ComputationalModel ⋯′ finPart keypairs as C
  renaming (K̂ to Kᵖʳⁱᵛ; K to Kᵖᵘᵇ)
  hiding (i; t; t′; `; ∣_∣; n; Run; Time; m; m′; λᶜ; Rᶜ; Value; ∎; R; R′; R″; Rᶜ′
        )
  hiding (_𝐁); _𝐁 = id -- ** for fast evaluation, i.e. type-checking

-- ** NB: cannot use this cause of different keys
-- open import Compiler.Example using (module TimedCommitment)
-- open TimedCommitment
-- open ∣K TC

open import BitML.Example.TimedCommitment
v = Value ∋ 1 𝐁; a♯ = + 9
open ∣K TC

T₀ : Tx 0 2
T₀ = record
  { inputs  = []
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ (1 , 1 𝐁 locked-by ƛ (versig [ K 0 ] [ 0 ]))
              ⨾ (1 , 0 𝐁 locked-by ƛ (versig [ K 1 ] [ 0 ]))
              ]
  ; absLock = 0 }

-- pre-existing deposits
Tᵃ Tᵇ : TxInput′
Tᵃ = (-, -, T₀) at 0F
Tᵇ = (-, -, T₀) at 1F

sechash : namesˡ G ↦ ℤ
sechash = λ where
  {- "a" -} 𝟘 → a♯

txout : namesʳ TC ↦ TxInput′
txout = λ where
  {- "x" -} 𝟘 → Tᵃ
  {- "y" -} 𝟙 → Tᵇ

out : InitTx G × (subterms⁺ C ↦′ BranchTx)
out = bitml-compiler {ad = TC} auto sechash txout K K²

outTxs : Tx 2 1 × Tx 1 1 × Tx 1 1 × Tx 1 1
outTxs = let t₀ , m = out in t₀ , m 0 , m 1 , m 2

Tᵢₙᵢₜ : Tx 2 1
Tᵢₙᵢₜ = sig⋆ [ [ K 0 ] ⨾ [ K 1 ] ] record
  { inputs  = hashTxⁱ <$> [ Tᵃ ⨾ Tᵇ ]
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ -, v locked-by ƛ (e₁ `∨ e₂)]
  ; absLock = 0 }
  where
    e₁ : Script 3 `Bool
    e₁ = versig (codom $ K² 0) [ 0 ⨾ 1 ]
      `∧ `true
      `∧ ⋀ [ hash (var 2) `= BTC.` (sechash 0) `∧ (BTC.` (+ η) `< BTC.∣ var 2 ∣) ]

    e₂ : Script 3 `Bool
    e₂ = versig (codom $ K² 2) [ 0 ⨾ 1 ]
Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

T′ : Tx 1 1
T′ = sig⋆ [ codom (K² 0) ] record
  { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ _ , v locked-by ƛ e′ ]
  ; absLock = 0 }
  where
    e′ : Script 2 `Bool
    e′ = versig (codom $ K² 1) [ 0 ⨾ 1 ]
T′♯ = (∃Tx ∋ -, -, T′) ♯

T′ᵃ : Tx 1 1
T′ᵃ = sig⋆ [ codom (K² 1) ] record
  { inputs  = [ T′♯ at 0 ]
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ 1 , v locked-by ƛ versig [ K 0 ] [ 0 ] ]
  ; absLock = 0 }

T′ᵇ : Tx 1 1
T′ᵇ = sig⋆ [ codom (K² 2) ] record
  { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ 1 , v locked-by ƛ versig [ K 1 ] [ 0 ] ]
  ; absLock = t }

_ = outTxs ≡ (Tᵢₙᵢₜ , T′ , T′ᵃ , T′ᵇ)
  ∋ refl

--

module Step₁ where
  Γ₀ Γₙ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y
  Γₙ = ⟨ A has 1 𝐁 ⟩at x₃ ∣ A ∶ a ♯ N

  _ : S.Run
  _ = record {start = Γ₀ at0; init = auto; end = Γₙ at0; trace = -, TC-stepsₜ}

  ℽ₀ : ℾᵗ (Γ₀ at0)
  ℽ₀ = [txout: (λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ) ∣sechash: (λ ()) ∣κ: (λ ()) ]

  Rᶜ₀ : C.Labels
  Rᶜ₀ = [ submit (-, -, T₀)
        ⨾ (A →∗∶ encode (Kᵖ A , K̂ᵖ A))
        ⨾ (B →∗∶ encode (Kᵖ B , K̂ᵖ B))
        ]

  cinit : Initial Rᶜ₀
  cinit = (-, -, T₀)
        , (λ where 𝟘 → 𝟘; 𝟙 → 𝟙)
        , refl

  Rˢ = (Γ₀ at0) ∎⊣ auto
  Rᶜ = CRun ∋ Rᶜ₀ ∎⊣ cinit ✓

  coh : Rˢ ~ Rᶜ
  coh = -, base {ℽ = ℽ₀} auto cinit
    λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl
  𝕣∗ = coh .proj₁

module Step₂ where
  module ≪ = Step₁
  𝕣 = ℝ∗⇒ℝ ≪.𝕣∗

  α  = advertise⦅ ⟨G⟩C ⦆
  Γ  = Cfg ∋ ` ⟨G⟩C ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 𝐁 ⟩at y
  Rˢ = (Γ at0) ⟨ Act {t = 0} $ C-Advertise {ad = ⟨G⟩C} {Γ = ≪.Γ₀} ⟩←—— ≪.Rˢ

  vad    = ValidAd ⟨G⟩C ∋ auto
  txoutΓ = Txout Γ    ∋ Txout≈ {≪.Rˢ ∙cfg}{≪.Γ₀} auto (𝕣 ∙txoutEnd_)
  txoutG = Txout ⟨G⟩C ∋ weaken-↦ txoutΓ (deposits⊆⇒namesʳ⊆ {⟨G⟩C}{≪.Γ₀} $ auto .unmk⊆)
  txoutC = Txout C    ∋ weaken-↦ txoutG (mapMaybe-⊆ isInj₂ $ vad ∙names-⊆)

  _C = encodeAd ⟨G⟩C (txoutG , txoutC)
  λᶜ = A →∗∶ _C
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂) ([L1] mkℍ)
  𝕣∗ = coh .proj₁

module Step₃ where
  module ≪ = Step₂

  Rˢ = ≪.Rˢ
  λᶜ = A →O∶ encode a
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₂ (≪.coh .proj₂) ([2] (inj₁ refl))
  𝕣∗ = coh .proj₁

module Step₄ where
  module ≪  = Step₃

  Rˢ = ≪.Rˢ
  λᶜ = O→ A ∶ a♯
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₂ (≪.coh .proj₂) ([2] (inj₂ refl))
  𝕣∗ = coh .proj₁

module Step₅ where
  module ≪≪ = Step₂
  module ≪  = Step₄
  open ℝ (ℝ∗⇒ℝ ≪.𝕣∗)

  Γ₀ Γ Γ′ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 𝐁 ⟩at y
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-commit⦅ A , ⟨G⟩C , [ a , just N ] ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ [C-AuthCommit] refl auto (λ _ → auto)

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  txoutGC = ad∈⇒Txout {⟨G⟩C}{≪≪.Γ}{≪.Rˢ}{0} (here refl) auto txout′
  txoutG  = txoutGC .proj₁; txoutC = txoutGC .proj₂
  _C      = encodeAd ⟨G⟩C txoutGC

  h̅ = List ℤ   ∋ [ a♯ ]
  k̅ = List ℤ   ∋ concatMap (map pub ∘ codom) (codom K²)

  C,h̅,k̅  = encode (_C , h̅ , k̅)
  C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ A) C,h̅,k̅

  λᶜ = A →∗∶ C,h̅,k̅ₐ
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L2] mkℍ {h = h} ∃B first-∃B [ h≡ ] first-λᶜ h∈O auto (λ ()))
    where
      h : H₂-args
      h = mk {⟨G⟩C}{Γ₀}{0}{A} K² [ a , just N , a♯ ] auto auto (λ _ → auto)
            (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)

      C≡ : _C ≡ ≪≪._C
      C≡ = encode-txout≡ ⟨G⟩C txoutG ≪≪.txoutG txoutC ≪≪.txoutC
            (λ where 𝟘 → refl; 𝟙 → refl) λ ()


      ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList ≪.Rᶜ
      ∃B rewrite C≡ = A , 𝟚

      first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ _C) (Any-tail $ ∃B .proj₂)
      first-∃B rewrite C≡ =
        [ (λ _ ())
        ⨾ (λ _ → label≢ encode≢)
        ⨾ (λ _ → label≢ encode≢)
        ]

      first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)
      first-λᶜ rewrite C≡ = [ (λ _ ()) ⨾ (λ _ ()) ]

      postulate
        h≡ : ∣ a♯ ∣ᵐ ≡ η
        ∣a∣ : ∣ encode a ∣ᵐ ≡ η + N

      h∈O : CheckOracleInteractions ≪.Rᶜ _
      h∈O = [ (A , encode a , 𝟘 , ∣a∣) ]

  𝕣∗ = coh .proj₁

module Step₆ where
  module ≪≪ = Step₂
  module ≪  = Step₅
  open ℝ (ℝ∗⇒ℝ ≪.𝕣∗)

  Γ₀ Γ Γ′ Γ″ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 𝐁 ⟩at y
     ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ ⟨G⟩C ]
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ ∅ᶜ ∣ B auth[ ♯▷ ⟨G⟩C ]
  Γ″ = ` ⟨G⟩C ∣ Γ₀ ∣ B auth[ ♯▷ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-commit⦅ B , ⟨G⟩C , [] ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ [C-AuthCommit] refl [] (λ _ → [])

  Rˢ = (Γ″ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  txoutGC = ad∈⇒Txout {⟨G⟩C}{≪.Γ′}{≪.Rˢ}{0} (here refl) auto txout′
  txoutG  = txoutGC .proj₁; txoutC = txoutGC .proj₂
  _C      = encodeAd ⟨G⟩C txoutGC

  h̅ = List ℤ   ∋ []
  k̅ = List ℤ   ∋ concatMap (map pub ∘ codom) (codom K²)

  C,h̅,k̅  = encode (_C , h̅ , k̅)
  C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ B) C,h̅,k̅

  λᶜ = B →∗∶ C,h̅,k̅ₐ
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L2] mkℍ {h = h} ∃B first-∃B [] first-λᶜ [] [] (λ ()))
    where
      h : H₂-args
      h = mk {⟨G⟩C}{Γ₀}{0}{B} K² [] refl [] (λ _ → [])
            (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ″ ⊣ auto)

      C≡ : _C ≡ ≪≪._C
      C≡ = encode-txout≡ ⟨G⟩C txoutG ≪≪.txoutG txoutC ≪≪.txoutC
            (λ where 𝟘 → refl; 𝟙 → refl) λ ()

      ∃B : ∃ λ B → (B →∗∶ _C) ∈ toList ≪.Rᶜ
      ∃B rewrite C≡ = A , 𝟛

      first-∃B : All (λ l → ∀ X → l ≢ X →∗∶ _C) (Any-tail $ ∃B .proj₂)
      first-∃B rewrite C≡ =
        [ (λ _ ())
        ⨾ (λ _ → label≢ encode≢)
        ⨾ (λ _ → label≢ encode≢)
        ]

      first-λᶜ : All (λ l → ∀ X → l ≢ X →∗∶ C,h̅,k̅ₐ) (Any-front $ ∃B .proj₂)
      first-λᶜ rewrite C≡ = [ (λ _ → label≢ SIG≢) ⨾ (λ _ ()) ⨾ (λ _ ()) ]
  𝕣∗ = coh .proj₁

module Step₇ where
  module ≪  = Step₆

  Rˢ = ≪.Rˢ
  λᶜ = A →∗∶ encode Tᵢₙᵢₜ
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₂ (≪.coh .proj₂) ([3] {A = A} (≁₁-encodeT Tᵢₙᵢₜ))
  𝕣∗ = coh .proj₁

module Step₈ where
  module ≪ = Step₇

  Γ₀ Γ Γ′ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 𝐁 ⟩at y
    ∣ ⟨ A ∶ a ♯ just 9 ⟩
    ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ A auth[ x ▷ˢ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-init⦅ A , ⟨G⟩C , x ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ C-AuthInit {Γ = Γ₀} {v = 1 𝐁}

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  λᶜ = A →∗∶ SIG (Kᵖʳⁱᵛ A) (∃Tx ∋ -, -, Tᵢₙᵢₜ)
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L3] mkℍ {h = h} (A , 𝟘) [])
    where
      h : H₃-args
      h = mk {⟨G⟩C}{Γ₀}{0}
            (auto .unmk⊆) 𝟘
            (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
  𝕣∗ = coh .proj₁

module Step₉ where
  module ≪ = Step₈

  Γ₀ Γ Γ′ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 𝐁 ⟩at y
    ∣ ⟨ A ∶ a ♯ just 9 ⟩
    ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]
    ∣ A auth[ x ▷ˢ ⟨G⟩C ]
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ B auth[ y ▷ˢ ⟨G⟩C ]

  committedA : partG ⊆ committedParticipants ⟨G⟩C Γ₀
  committedA = auto .unmk⊆

  Γ→ : Γ at0 —[ auth-init⦅ B , ⟨G⟩C , y ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ [C-AuthInit] {Γ = Γ₀} {v = 0 𝐁} committedA 𝟙

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  T  = ∃Tx ∋ -, -, Tᵢₙᵢₜ
  m  = SIG (Kᵖʳⁱᵛ B) T
  λᶜ = B →∗∶ m
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L3] mkℍ {h = h} (A , 𝟙) [ (λ _ → label≢ SIG≢) ] )
    where
      h : H₃-args
      h = mk {⟨G⟩C}{Γ₀}{0}{B}{y}{0 𝐁}
            committedA 𝟙
            (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
  𝕣∗ = coh .proj₁

module Step₁₀ where
  module ≪ = Step₉

  Γ Γ′ : Cfg
  Γ  = ` ⟨G⟩C
    ∣ ⟨ A ∶ a ♯ just 9 ⟩
    ∣ ((⟨ A has 1 𝐁 ⟩at x ∣ A auth[ x ▷ˢ ⟨G⟩C ])
      ∣ (⟨ B has 0 𝐁 ⟩at y ∣ B auth[ y ▷ˢ ⟨G⟩C ]))
    ∣ (A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ])
  Γ′ = ⟨ C , 1 𝐁 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩

  fresh-x₁ : x₁ ∉ [ x ⨾ y ] ++ ids ⟨ A ∶ a ♯ just 9 ⟩
  fresh-x₁ = auto

  Γ→ : Γ at0 —[ init⦅ G , C ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ [C-Init] {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} fresh-x₁

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  T  = ∃Tx ∋ -, -, Tᵢₙᵢₜ
  λᶜ = submit (-, -, Tᵢₙᵢₜ)
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L4] mkℍ {h = h})
    where
      h : H₄-args
      h = mk {⟨G⟩C}{⟨ A ∶ a ♯ just 9 ⟩}{0}{x₁}
             fresh-x₁
             (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
  𝕣∗ = coh .proj₁

module Step₁₁ where
  module ≪≪ = Step₆
  module ≪  = Step₁₀

  Γ Γ′ : Cfg
  Γ  = ⟨ A ∶ a ♯ just 9 ⟩ ∣ ⟨ C , 1 𝐁 ⟩at x₁
  Γ′ = A ∶ a ♯ 9 ∣ ⟨ C , 1 𝐁 ⟩at x₁

  Γ→ : Γ at0 —[ auth-rev⦅ A , a ⦆ ]→ₜ Γ′ at0
  Γ→ = Act [C-AuthRev]

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  λᶜ = A →∗∶ encode a
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  postulate instance Tx≢String : ∀ {i o} → Tx i o ≢′ String

  coh : _ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L7] mkℍ {h = h} (A , ≪≪.txoutGC , 𝟝) 𝟘 m≥ (A , 𝟘)
      [ (λ _ ())
      ⨾ (λ _ → label≢ SIG≢encode)
      ⨾ (λ _ → label≢ SIG≢encode)
      ⨾ (λ _ → label≢ encode≢)
      ⨾ (λ _ → label≢ SIG≢encode)
      ])
    where
      h : H₇-args
      h = mk {⟨G⟩C}{A}{a}{9}{⟨ C , 1 𝐁 ⟩at x₁}{0} K² [ a , just 9 , a♯ ]
             (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
             𝟙

      postulate m≥ : ∣ encode a ∣ᵐ Nat.≥ η
  𝕣∗ = coh .proj₁

module Step₁₂ where
  module ≪ = Step₁₁

  Γ Γ′ : Cfg
  Γ  = ⟨ C , 1 𝐁 ⟩at x₁ ∣ (∅ᶜ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ))
  Γ′ = ⟨ [ withdraw A ] , 1 𝐁 ⟩at x₂ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ)

  Γ→ : Γ at0 —[ put⦅ [] , [ a ] , x₁ ⦆ ]→ₜ Γ′ at0
  Γ→ = Timeout {c = C} {t = 0} {v = 1} {i = 0F}
     $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]}

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  T  = ∃Tx ∋ -, -, T′
  λᶜ = submit T
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : _ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L6] mkℍ {h = h})
    where
      h : H₆-args
      h = mk {C}{1 𝐁}{x₁}{[ withdraw A ]}{x₂}{A ∶ a ♯ 9}{0}{i = 0F}
             refl refl auto refl refl
             (≪.Rᶜ ⨾ _ ⨾ _ ⊣ auto ≈ Γ′ ⊣ auto)
  𝕣∗ = coh .proj₁

-- module Step₁₃ where
--   module ≪ = Step₁₂

--   Γ Γ′ : Cfg
--   Γ  = ⟨ [ withdraw A ] , 1 𝐁 ⟩at x₂ ∣ A ∶ a ♯ 9
--   Γ′ = ⟨ A has 1 𝐁 ⟩at x₃ ∣ A ∶ a ♯ 9

--   Γ→ : Γ at0 —[ α ]→ₜ Γ′ at0
--   Γ→ = Timeout {i = 0} [C-Withdraw]

--   Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

--   λᶜ = submit (-, -, T′ᵃ)
--   Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

--   coh : Rˢ ~ Rᶜ
--   coh = -, step₁ (≪.coh .proj₂)
--     ([L9] mkℍ {h = h})
--     where
--       h : H₉-args
--       h = mk {[ withdraw A ]}{1 𝐁}{x₂}{A ∶ a ♯ 9}{A}{x₃}{0}{i = 0F}
--             refl auto refl []
--             (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
--   𝕣∗ = coh .proj₁
