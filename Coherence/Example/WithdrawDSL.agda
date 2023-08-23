-- only scope check
module Coherence.Example.WithdrawDSL where

open import Coherence.Example.Setup
open import SymbolicModel ⋯′ as S
  hiding ( C; G; t; a; v; A; B; x; y; Γ₀; Γₜ₀; Δ; Γₜ; Γₜ′; as; α; Γ; Γ′
          ; _`=_; _`∧_; _`∨_; `true; _`<_
          ; Rˢ; Rˢ′; Σ
          )
open import ComputationalModel ⋯′ finPart keypairs as C
  renaming (K̂ to Kᵖʳⁱᵛ; K to Kᵖᵘᵇ)
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

⟨G⟩C′ = encodeAd ⟨G⟩C (txoutG , txoutC)
C,h̅,k̅ = encode {A = Message × List HashId × List HashId}
               (⟨G⟩C′ , [] , concatMap (map pub ∘ codom) (codom K²))

_ : _ ~ _
_ =
  ∎   (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y) at0
      ⊣ auto , [txout: (λ where 𝟘 → Tˣ; 𝟙 → Tʸ) ∣sechash: (λ ()) ∣κ: (λ ()) ]
    ~ [ submit (-, -, T₀)
      ⨾ (A →∗∶ encode (Kᵖ A , K̂ᵖ A))
      ⨾ (B →∗∶ encode (Kᵖ B , K̂ᵖ B))
      ] ⊣ (-, (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
    ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

  —→  (` ⟨G⟩C ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y) at0
      ⊣ ((advertise⦅ ⟨G⟩C ⦆ , _) , _)
    ~ (A →∗∶ ⟨G⟩C′)
    ⊣ [L1] mkℍ {h = mk {⟨G⟩C}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y}
               auto auto (auto .unmk⊆) _}

  —→  (` ⟨G⟩C ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 ⟩at y
              ∣ A auth[ ♯▷ ⟨G⟩C ]) at0
      ⊣ ((auth-commit⦅ A , ⟨G⟩C , [] ⦆ , _) , _)
    ~ (A →∗∶ SIG (Kᵖᵘᵇ A) C,h̅,k̅)
    ⊣ [L2] mkℍ {h = mk {⟨G⟩C} K² _ _ _ _ _}
               (A , 𝟘)
               [ (λ _ ()) ⨾ (λ _ → label≢ encode≢) ⨾ (λ _ → label≢ encode≢) ]
               [] [] [] [] (λ ())

  —→  (` ⟨G⟩C ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 ⟩at y
              ∣ A auth[ ♯▷ ⟨G⟩C ]) ∣ B auth[ ♯▷ ⟨G⟩C ]) at0
      ⊣ ((auth-commit⦅ B , ⟨G⟩C , [] ⦆ , _) , _)
    ~ (B →∗∶ SIG (Kᵖᵘᵇ B) C,h̅,k̅)
    ⊣ [L2] mkℍ {h = mk {⟨G⟩C} K² _ _ _ _ _}
               (A , 𝟙)
               [ (λ _ ()) ⨾ (λ _ → label≢ encode≢) ⨾ (λ _ → label≢ encode≢) ]
               [] [ (λ _ → label≢ SIG≢) ] [] [] (λ ())

  —→ᵋ (A →∗∶ encode Tᵢₙᵢₜ)
    ⊣ [3] {A = A} (≁₁-encodeT Tᵢₙᵢₜ)

  —→  (` ⟨G⟩C ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 ⟩at y
              ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ])
              ∣ A auth[ x ▷ˢ ⟨G⟩C ]) at0
      ⊣ ((auth-init⦅ A , ⟨G⟩C , x ⦆ , _) , _)
    ~ (A →∗∶ SIG (Kᵖʳⁱᵛ A) (∃Tx ∋ -, -, Tᵢₙᵢₜ))
    ⊣ [L3] mkℍ {h = h₃} (A , 𝟘) []

  —→  (` ⟨G⟩C ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 ⟩at y
              ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]
              ∣ A auth[ x ▷ˢ ⟨G⟩C ]) ∣ B auth[ y ▷ˢ ⟨G⟩C ]) at0
            ⊣ ((auth-init⦅ B , ⟨G⟩C , y ⦆ , _) , _)
    ~ (B →∗∶ SIG (Kᵖʳⁱᵛ B) (∃Tx ∋ -, -, Tᵢₙᵢₜ))
    ⊣ [L3] mkℍ {h = h₃′} (A , 𝟙) [ (λ _ → label≢ SIG≢) ]

  —→  (⟨ C , 2 𝐁 ⟩at x₁ ∣ ∅ᶜ) at0
      ⊣ ((init⦅ G , C ⦆ , _) , _)
    ~ submit (-, -, Tᵢₙᵢₜ)
    ⊣ [L4] mkℍ {h = mk {⟨G⟩C} auto _}

  —→  (⟨ B has 2 𝐁 ⟩at x₂ ∣ ∅ᶜ) at0
      ⊣ ((withdraw⦅ B , 2 𝐁 , x₁ ⦆ , _) , _)
    ~ submit (-, -, Tᵇ)
    ⊣ [L9] mkℍ {h = h₉}

    where
      h₃ : H₃-args
      h₃ = mk {Γ₀ = ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y
                  ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]}
              (auto .unmk⊆) 𝟘 _

      h₃′ : H₃-args
      h₃′ = mk {⟨G⟩C}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 1 𝐁 ⟩at y
                     ∣ A auth[ ♯▷ ⟨G⟩C ] ∣ B auth[ ♯▷ ⟨G⟩C ]
                     ∣ A auth[ x ▷ˢ ⟨G⟩C ]}{0} ? 𝟙
               (_ ⨾ _ ⨾ _ ⊣ auto ≈ ` ⟨G⟩C ∣ _ ∣ B auth[ y ▷ˢ ⟨G⟩C ] ⊣ auto)

      h₉ : H₉-args
      h₉ = mk {C}{2 𝐁}{x₁}{∅ᶜ}{B}{x₂}{0}{i = 0F} refl auto refl []
              (_ ⨾ _ ⨾ _ ⊣ auto ≈ (⟨ B has 2 𝐁 ⟩at x₂ ∣ ∅ᶜ) ⊣ auto)
