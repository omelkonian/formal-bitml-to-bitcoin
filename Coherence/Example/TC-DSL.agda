-- only scope check
module Coherence.Example.TC-DSL where

import Bitcoin as BTC
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

txoutTC = Txout TC ∋ λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ
txoutC  = Txout C  ∋ λ ()
txoutG  = Txout G  ∋ λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ

TC′ = encodeAd TC (txoutG , txoutC)
C,h̅,k̅ = encode {A = Message × List HashId × List HashId}
               (TC′ , [ a♯ ] , concatMap (map pub ∘ codom) (codom K²))

_ : _ ~ _
_ =
  ∎   (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y) at0
      ⊣ auto , [txout: (λ where 𝟘 → Tᵃ; 𝟙 → Tᵇ) ∣sechash: (λ ()) ∣κ: (λ ()) ]
    ~ [ submit (-, -, T₀)
      ⨾ (A →∗∶ encode (Kᵖ A , K̂ᵖ A))
      ⨾ (B →∗∶ encode (Kᵖ B , K̂ᵖ B))
      ] ⊣ ((-, -, T₀) , (λ where 𝟘 → 𝟘; 𝟙 → 𝟙) , refl)
    ⊣ (λ where 𝟘 → 0F , refl , refl; 𝟙 → 1F , refl , refl)

  —→  (` TC ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y) at0
      ⊣ ((advertise⦅ TC ⦆ , _) , _)
    ~ (A →∗∶ TC′)
    ⊣ [L1] mkℍ {h = mk {TC}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 𝐁 ⟩at y}
               auto auto (auto .unmk⊆) _}

  —→ᵋ (A →O∶ encode a)
    ⊣ [2] (inj₁ refl)

  —→ᵋ (O→ A ∶ a♯)
    ⊣ [2] (inj₂ refl)

  —→  (` TC ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y
            ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ]) at0
      ⊣ ((auth-commit⦅ A , TC , [ a , just N ] ⦆ , _) , _)
    ~ (A →∗∶ SIG (Kᵖᵘᵇ A) C,h̅,k̅)
    ⊣ [L2] mkℍ {h = h₂}
               (A , 𝟚)
               [ (λ _ ()) ⨾ (λ _ → label≢ encode≢) ⨾ (λ _ → label≢ encode≢) ]
               [ h≡ ] [ (λ _ ()) ⨾ (λ _ ()) ] [ (A , encode a , 𝟘 , ∣a∣) ] auto (λ ())

  —→  (` TC ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y
            ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ])
            ∣ B auth[ ♯▷ TC ]) at0
            ⊣ ((auth-commit⦅ B , TC , [] ⦆ , _) , _)
    ~ (B →∗∶ SIG (Kᵖᵘᵇ B) C,h̅,k̅)
    ⊣ [L2] mkℍ {h = h₂′}
               (A , 𝟛)
               [ (λ _ ()) ⨾ (λ _ → label≢ encode≢) ⨾ (λ _ → label≢ encode≢) ]
               [] [ (λ _ → label≢ SIG≢) ⨾ (λ _ ()) ⨾ (λ _ ()) ] [] [] (λ ())

  —→ᵋ (A →∗∶ encode Tᵢₙᵢₜ)
    ⊣ [3] {A = A} (≁₁-encodeT Tᵢₙᵢₜ)

  —→  (` TC ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
            ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ])
            | A auth[ x ▷ˢ TC ]) at0
            ⊣ ((auth-init⦅ B , TC , y ⦆ , _) , _)
    ~ (A →∗∶ SIG (Kᵖʳⁱᵛ A) (∃Tx ∋ -, -, Tᵢₙᵢₜ))
    ⊣ [L3] mkℍ {h = h₃} (A , 𝟘) []

  —→  (` TC ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
            ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]
            | A auth[ x ▷ˢ TC ]) | B auth[ y ▷ˢ TC ]) at0
            ⊣ ((auth-init⦅ B , TC , y ⦆ , _) , _)
    ~ (B →∗∶ SIG (Kᵖʳⁱᵛ B) (∃Tx ∋ -, -, Tᵢₙᵢₜ))
    ⊣ [L3] mkℍ {h = h₃′} (A , 𝟙) [ (λ _ → label≢ SIG≢) ]

  —→  (⟨ C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩) at0
      ⊣ ((init⦅ G , C ⦆ , _) , _)
    ~ submit (-, -, Tᵢₙᵢₜ)
    ⊣ [L4] mkℍ {h = h₄}

  —→  (⟨ C , 1 ⟩at x₁ ∣ A ∶ a ♯ N) at0
      ⊣ ((auth-rev⦅ A , a ⦆ , _) , _)
    ~ (A →∗∶ encode a)
    ⊣ [L7] mkℍ {h = h₇} (A , txoutTC , 𝟝) 𝟘 m≥ (A , 𝟘)
          [ (λ _ ())
          ⨾ (λ _ → label≢ SIG≢encode)
          ⨾ (λ _ → label≢ SIG≢encode)
          ⨾ (λ _ → label≢ encode≢)
          ⨾ (λ _ → label≢ SIG≢encode)
          ]

  —→  (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ N) at0
      ⊣ ((put⦅ [] , [ a ] , x₁ ⦆ , _) , _)
    ~ submit (-, -, T′)
    ⊣ [L6] mkℍ {h = h₆}

  —→  (⟨ A has 1 𝐁 ⟩at x₃ ∣ A ∶ a ♯ N) at0
      ⊣ ((withdraw⦅ A , 1 𝐁 , x₂ ⦆ , _) , _)
    ~ submit (-, -, T′ᵃ)
    ⊣ [L9] mkℍ {h = h₉}

    where
      h₂ : H₂-args
      h₂ = mk {TC}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y}
              {0}{A} K² [ a , just N , a♯ ] auto auto (λ _ → auto)
              (_ ⨾ _ ⨾ _ ⊣ auto
              ≈ ` TC ∣ ⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y
                     ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ] ⊣ auto)
      postulate
        h≡ : ∣ a♯ ∣ᵐ ≡ η
        ∣a∣ : ∣ encode a ∣ᵐ ≡ η + N

      h₂′ : H₂-args
      h₂′ = mk {TC}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y
                     ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ]}
               {0}{B} K² [] refl [] (λ _ → [])
               ( _ ⨾ _ ⨾ _ ⊣ auto
               ≈ (` TC ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y
                       ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ])
                       ∣ B auth[ ♯▷ TC ]) ⊣ auto)
      h₃ : H₃-args
      h₃ = mk {TC}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                    ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]}{0}
              (auto .unmk⊆) 𝟘
              (_ ⨾ _ ⨾ _ ⊣ auto
              ≈ (` TC ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                      ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ])
                      ∣ A auth[ x ▷ˢ TC ]) ⊣ auto)
      h₃′ : H₃-args
      h₃′ = mk {TC}{⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                    ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]}
               {0}{B}{y}{0 𝐁}
               (auto .unmk⊆) 𝟙
               (_ ⨾ _ ⨾ _ ⊣ auto
               ≈ (` TC ∣ (⟨ A has 1 𝐁 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                       ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]
                       ∣ A auth[ x ▷ˢ TC ]) ∣ B auth[ y ▷ˢ TC ]) ⊣ auto)
      h₄ : H₄-args
      h₄ = mk {TC}{⟨ A ∶ a ♯ just N ⟩}{0}{x₁}
              auto
              (_ ⨾ _ ⨾ _ ⊣ auto
              ≈ (⟨ C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩) ⊣ auto)

      h₆ : H₆-args
      h₆ = mk {C}{1 𝐁}{x₁}{[ withdraw A ]}{x₂}{A ∶ a ♯ N}{0}{i = 0F}
              refl refl auto refl refl
              (_ ⨾ _ ⨾ _ ⊣ auto ≈ (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ N) ⊣ auto)

      h₇ : H₇-args
      h₇ = mk {TC}{A}{a}{N}{⟨ C , 1 𝐁 ⟩at x₁}{0} K² [ a , just N , a♯ ]
              (_ ⨾ _ ⨾ _ ⊣ auto
              ≈ (⟨ C , 1 ⟩at x₁ ∣ A ∶ a ♯ N) ⊣ auto)
              𝟙

      postulate m≥ : ∣ encode a ∣ᵐ Nat.≥ η

      h₉ : H₉-args
      h₉ = mk {[ withdraw A ]}{1 𝐁}{x₂}{A ∶ a ♯ N}{A}{x₃}{0}{i = 0F}
              refl auto refl []
              (_ ⨾ _ ⨾ _ ⊣ auto ≈ (⟨ A has 1 𝐁 ⟩at x₃ ∣ A ∶ a ♯ N) ⊣ auto)
