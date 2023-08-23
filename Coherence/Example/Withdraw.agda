module Coherence.Example.Withdraw where

open import Coherence.Example.Setup
open import SymbolicModel ⋯′
  hiding ( C; G; t; a; v; A; B; x; y; Γ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′
          ; _`=_; _`∧_; _`∨_; `true; _`<_
          ; Rˢ; Rˢ′; Σ; Γ″
          )
open import ComputationalModel ⋯′ finPart keypairs
  renaming (K̂ to Kᵖʳⁱᵛ; K to Kᵖᵘᵇ; Label to CLabel; Labels to CLabels)
  hiding (i; t; t′; `; ∣_∣; n; Run; Time; m; m′; λᶜ; Rᶜ; Value; ∎; R; R′; R″; Rᶜ′
        )
  hiding (_𝐁); _𝐁 = id -- ** for fast evaluation, i.e. type-checking

-- ** NB: cannot use this cause of different keys
-- open import Compiler.Example using (module Section7)
-- open Section7.Withdraw
-- open ∣K ex-ad

x = "x"; y = "y"; x₁ = "x₁"; x₂ = "x₂"

open ∣K (⟨ A :! 1 𝐁 at x ∣ B :! 1 𝐁 at y ⟩ [ withdraw B ])

T₀ : Tx 0 2
T₀ = record
  { inputs  = []
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ (1 , 1 𝐁 locked-by ƛ (versig [ K 0 ] [ 0 ]))
              ⨾ (1 , 1 𝐁 locked-by ƛ (versig [ K 1 ] [ 0 ]))
              ]
  ; absLock = 0 }

Tˣ Tʸ : TxInput′
Tˣ = (-, -, T₀) at 0
Tʸ = (-, -, T₀) at 1

sechash : secrets G ↦ ℤ
sechash ()

txout : ids G ↦ TxInput′
txout = λ where
  {- "x" -} 𝟘 → Tˣ
  {- "y" -} 𝟙 → Tʸ

out : InitTx G × (subterms⁺ C ↦′ BranchTx)
out = bitml-compiler {ad = ⟨G⟩C} auto sechash txout K K²

outTxs : Tx 2 1 × Tx 1 1
outTxs = let t₀ , m = out in t₀ , m 0

Tᵢₙᵢₜ : Tx 2 1
Tᵢₙᵢₜ = sig⋆ [ [ K 0 ] ⨾ [ K 1 ] ] record
  { inputs  = hashTxⁱ <$> [ Tˣ ⨾ Tʸ ]
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ 2 , 2 𝐁 locked-by ƛ versig (codom $ K² 0) [ 0 ⨾ 1 ] ]
  ; absLock = 0 }
Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

Tᵇ : Tx 1 1
Tᵇ = sig⋆ [ codom (K² 0) ] record
  { inputs  = [ Tᵢₙᵢₜ♯ at 0 ]
  ; wit     = wit⊥
  ; relLock = V.replicate 0
  ; outputs = [ 1 , 2 𝐁 locked-by ƛ versig [ K 1 ] [ 0 ] ]
  ; absLock = 0 }

_ = outTxs ≡ (Tᵢₙᵢₜ , Tᵇ)
  ∋ refl

--

txoutGC = Txout ⟨G⟩C ∋ λ where 𝟘 → Tˣ; 𝟙 → Tʸ
txoutC  = Txout C    ∋ λ ()
txoutG  = Txout G    ∋ λ where 𝟘 → Tˣ; 𝟙 → Tʸ
GC      = encodeAd ⟨G⟩C (txoutG , txoutC)

module Step₁ where
  Γ₀ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y

  ℽ₀ : ℾᵗ (Γ₀ at0)
  ℽ₀ = [txout: (λ where 𝟘 → Tˣ; 𝟙 → Tʸ) ∣sechash: (λ ()) ∣κ: (λ ()) ]

  Rᶜ₀ : CLabels
  Rᶜ₀ = [ submit (-, -, T₀)
        ⨾ (A →∗∶ encode (Kᵖ A , K̂ᵖ A))
        ⨾ (B →∗∶ encode (Kᵖ B , K̂ᵖ B))
        ]

  cinit : Initial Rᶜ₀
  cinit = -, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl

  Rˢ = (Γ₀ at0) ∎⊣ auto

  Rᶜ : CRun
  Rᶜ = Rᶜ₀ ∎⊣ cinit ✓

  coh : Rˢ ~ Rᶜ
  coh = -, base {ℽ = ℽ₀} auto cinit
    λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl
  𝕣∗ = coh .proj₁

module Step₂ where
  module ≪ = Step₁

  Γ  = Cfg ∋ ` ⟨G⟩C ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y
  Rˢ = (Γ at0) ⟨ Act {t = 0} $ C-Advertise {ad = ⟨G⟩C} {Γ = ≪.Γ₀} ⟩←—— ≪.Rˢ

  λᶜ = A →∗∶ GC
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂) ([L1] mkℍ)
  𝕣∗ = coh .proj₁

module Step₃ where
  module ≪ = Step₂

  Γ₀ Γ Γ′ Γ″ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ ∅ᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
  Γ″ = ` ⟨G⟩C ∣ Γ₀ ∣ A auth[ ♯▷ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-commit⦅ A , ⟨G⟩C , [] ⦆ ]→ₜ Γ′ at0
  Γ→ = Act C-AuthCommit

  Rˢ = (Γ″ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  h̅ = List ℤ ∋ []
  k̅ = List ℤ ∋ concatMap (map pub ∘ codom) (codom K²)

  C,h̅,k̅  = encode (GC , h̅ , k̅)
  C,h̅,k̅ₐ = SIG (Kᵖᵘᵇ A) C,h̅,k̅

  λᶜ = A →∗∶ C,h̅,k̅ₐ
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L2] mkℍ
      {h = mk {⟨G⟩C} K² _ _ _ _ _}
      (A , 𝟘) [ (λ _ ()) ⨾ (λ _ → label≢ encode≢) ⨾ (λ _ → label≢ encode≢) ]
      [] [] [] [] (λ ()))
  𝕣∗ = coh .proj₁

module Step₄ where
  module ≪ = Step₃

  Γ₀ Γ Γ′ Γ″ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y ∣ A auth[ ♯▷ ⟨G⟩C ]
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ ∅ᶜ ∣ B auth[ ♯▷ ⟨G⟩C ]
  Γ″ = ` ⟨G⟩C ∣ Γ₀ ∣ B auth[ ♯▷ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-commit⦅ B , ⟨G⟩C , [] ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ [C-AuthCommit] refl [] (λ _ → [])

  Rˢ = (Γ″ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  h̅ = List ℤ   ∋ []
  k̅ = List ℤ   ∋ concatMap (map pub ∘ codom) (codom K²)

  C,h̅,k̅ = SIG (Kᵖᵘᵇ B) $ encode (GC , h̅ , k̅)
  λᶜ = B →∗∶ C,h̅,k̅
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L2] mkℍ
      {h = mk {⟨G⟩C} K² _ _ _ _ _}
      (A , 𝟙) [ (λ _ ()) ⨾ (λ _ → label≢ encode≢) ⨾ (λ _ → label≢ encode≢) ]
      [] [ (λ _ → label≢ SIG≢) ] [] [] (λ ()))
  𝕣∗ = coh .proj₁

module Step₅ where
  module ≪ = Step₄

  Rˢ = ≪.Rˢ
  λᶜ = A →∗∶ encode Tᵢₙᵢₜ
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₂ (≪.coh .proj₂) ([3] {A = A} (≁₁-encodeT Tᵢₙᵢₜ))
  𝕣∗ = coh .proj₁

module Step₆ where
  module ≪ = Step₅

  Γ₀ Γ Γ′ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ A auth[ x ▷ˢ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-init⦅ A , ⟨G⟩C , x ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ C-AuthInit {Γ = Γ₀} {v = 1 𝐁}

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  m  = SIG (Kᵖʳⁱᵛ A) (∃Tx ∋ -, -, Tᵢₙᵢₜ)
  λᶜ = A →∗∶ m
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L3] mkℍ {h = h} (A , 𝟘) [])
    where h : H₃-args
          h = mk {Γ₀ = Γ₀} (auto .unmk⊆) 𝟘 _
  𝕣∗ = coh .proj₁

module Step₇ where
  module ≪ = Step₆

  Γ₀ Γ Γ′ : Cfg
  Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]
     ∣ A auth[ x ▷ˢ ⟨G⟩C ]
  Γ  = ` ⟨G⟩C ∣ Γ₀
  Γ′ = ` ⟨G⟩C ∣ Γ₀ ∣ B auth[ y ▷ˢ ⟨G⟩C ]

  Γ→ : Γ at0 —[ auth-init⦅ B , ⟨G⟩C , y ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ C-AuthInit {Γ = Γ₀} {v = 1 𝐁}

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  λᶜ = B →∗∶ SIG (Kᵖʳⁱᵛ B) (∃Tx ∋ -, -, Tᵢₙᵢₜ)
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : _ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L3] mkℍ {h = h} (A , 𝟙) [ (λ _ → label≢ SIG≢) ])
    where h : H₃-args
          h = mk {⟨G⟩C}{Γ₀}{0}
                 (auto .unmk⊆) 𝟙
                 (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
  𝕣∗ = coh .proj₁

module Step₈ where
  module ≪ = Step₇

  Γ Γ′ : Cfg
  Γ  = ` ⟨G⟩C
     ∣ ∅ᶜ
     ∣ ((⟨ A has 1 𝐁 ⟩at x ∣ A auth[ x ▷ˢ ⟨G⟩C ])
       ∣ (⟨ B has 1 𝐁 ⟩at y ∣ B auth[ y ▷ˢ ⟨G⟩C ]))
     ∣ (A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ])
  Γ′ = ⟨ C , 2 𝐁 ⟩at x₁ ∣ ∅ᶜ

  Γ→ : Γ at0 —[ init⦅ G , C ⦆ ]→ₜ Γ′ at0
  Γ→ = Act $ C-Init {x = x₁} {Γ = ∅ᶜ}

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  λᶜ = submit (-, -, Tᵢₙᵢₜ)
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : Rˢ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L4] mkℍ {h = mk {⟨G⟩C} auto _})
  𝕣∗ = coh .proj₁

module Step₉ where
  module ≪ = Step₈

  Γ Γ′ : Cfg
  Γ  = ⟨ C , 2 𝐁 ⟩at x₁ ∣ ∅ᶜ
  Γ′ = ⟨ B has 2 𝐁 ⟩at x₂ ∣ ∅ᶜ

  Γ→ : Γ at0 —[ withdraw⦅ B , 2 𝐁 , x₁ ⦆ ]→ₜ Γ′ at0
  Γ→ = Timeout {i = 0} C-Withdraw

  Rˢ = (Γ′ at0) ⟨ Γ→ ⟩←—— ≪.Rˢ

  λᶜ = submit (-, -, Tᵇ)
  Rᶜ = λᶜ ∷ ≪.Rᶜ ✓

  coh : _ ~ Rᶜ
  coh = -, step₁ (≪.coh .proj₂)
    ([L9] mkℍ {h = h})
    where h : H₉-args
          h = mk {C}{2 𝐁}{x₁}{∅ᶜ}{B}{x₂}{0}{i = 0F}
                 refl auto refl []
                 (≪.Rᶜ ⨾ ≪.Rˢ ⨾ ≪.𝕣∗ ⊣ auto ≈ Γ′ ⊣ auto)
