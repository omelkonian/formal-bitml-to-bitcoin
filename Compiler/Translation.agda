----------------------------------------------------------------------------
-- Compiler from BitML to Bitcoin transactions (see BitML paper, Section 7).
----------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open L.SubS using (⊆-refl)
open L.Mem hiding (mapWith∈)
open L.Any using (index)
open L.All using (lookup)
open F using (inject+; raise)
open V using (replicate)
open V.Any using (fromList⁻)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Lists.Collections
open import Prelude.Membership using (mapWith∈)
open import Prelude.Validity
open import Prelude.FromList
open import Prelude.Num

open import Bitcoin hiding (Value; Time; index)

open import BitML.BasicTypes using (⋯)

module Compiler.Translation

  -- BitML parameters
  (⋯ : ⋯) (let open ⋯ ⋯)

  -- Compilation parameters
  (η : ℕ) -- public security nonce η, ensures adversaries cannot guess
  where

open import BitML ⋯ hiding (`_; _`+_; _`-_; `true; _`∧_; _`<_; _`=_; xs; v′)
open Induction hiding (D; C; V)

open import Compiler.Mappings ⋯
open import Compiler.Outputs ⋯

bitml-compiler : let ⟨ g ⟩ c = ad in
    -- the input contract & precondition (only compile valid advertisements)
    Valid ad
    -- sechash: maps secrets in G to the corresponding committed hashes
  → (sechash : Sechash g)
    -- txout: maps deposits in G to existing transactions with the corresponding value
  → (txout : Txout g)
    -- Exchanged keypairs K(A) and K(D,A)
  → (K : 𝕂 g)
  → (K² : 𝕂²′ ad)
    -- a set of transactions to be submitted
  → InitTx g × (subterms⁺ c ↦′ BranchTx)
bitml-compiler {ad = ⟨ G₀ ⟩ C₀} vad sechash₀ txout₀ K K² =
  Tᵢₙᵢₜ , (≺-rec _ go) (ℂ.C C₀) record
    { T,o     = Tᵢₙᵢₜ♯ at 0
    ; curV    = v₀
    ; P       = partG , ⊆-refl
    ; curT    = 0
    ; p⊆      = nub-⊆⁺ ∘ Valid⇒part⊆ vad
    ; s⊆      = id
    ; ∃s      = tt
    ; sechash = sechash₀ ∘ mapMaybe-⊆ isInj₁ names⊆
    ; txout   = txout₀   ∘ mapMaybe-⊆ isInj₂ names⊆
    ; part    = part₀    ∘ mapMaybe-⊆ isInj₂ names⊆
    ; val     = val₀     ∘ mapMaybe-⊆ isInj₂ names⊆ }
  where
    names⊆ = vad .names-⊆ .unmk⊆
    xs = persistentIds G₀

    partG = nub-participants G₀
    ς     = length partG
    v₀    = sum $ (proj₁ ∘ proj₂) <$> persistentDeposits G₀

    -- part: maps deposit names in G to the corresponding participant
    part₀ : ids G₀ ↦ ∃ (_∈ partG)
    part₀ = -,_ ∘ ∈-nub⁺ ∘ proj₂ ∘ getDeposit {g = G₀}

    -- val: maps deposit names in G to the value contained in the deposit
    val₀ : ids G₀ ↦ Value
    val₀ = proj₁ ∘ proj₂ ∘ proj₁ ∘ getDeposit {g = G₀}

    -- Bₒᵤₜ
    Bₒᵤₜ : subterms C₀ ↦ (∃[ ctx ] Script ctx `Bool)
    Bₒᵤₜ {D} D∈ with removeTopDecorations D in D≡
    ... | put zs &reveal as if p ⇒ _
        = (ς + m)
        ,   versig (mapWith∈ partG $ K² D∈) (inject+ m <$> allFin ς)
         `∧ Bᵖʳ p p⊆as
         `∧ ⋀ (mapEnumWith∈ as $ λ i a a∈ → let bi = var (raise ς i) in
                   hash bi `= ` (sechash₀ $ as⊆ a∈)
                `∧ ` (+ η) `< ∣ bi ∣)
      where
        m = length as

        p⊆ : putComponents D ⊆ putComponents C₀
        p⊆ = subterms-putComponents⊆ᶜ {ds = C₀} D∈

        n⊆ : names D ⊆ names C₀
        n⊆ = subterms-names⊆ᶜ {d = D} {ds = C₀} D∈

        put∈ : (zs , as , p) ∈ putComponents D
        put∈ rewrite remove-putComponents {D} | D≡ = 0

        p⊆as : secrets p ⊆ as
        p⊆as = lookup (vad .names-put) (p⊆ put∈) .proj₂ .unmk⊆

        as⊆ : as ⊆ secrets G₀
        as⊆ = (λ x → ∈-mapMaybe⁺ isInj₁ x refl) ∘ names⊆ ∘ n⊆ ∘ as⊆′ ∘ ∈-map⁺ inj₁
          where
            as⊆′ : map inj₁ as ⊆ names D
            as⊆′ rewrite remove-names {D} | D≡ = ∈-++⁺ʳ (inj₂ <$> zs) ∘ ∈-++⁺ˡ

        Bᵃʳ : (e : Arith) → secrets e ⊆ as → Script (ς + m) `ℤ
        Bᵃʳ = λ where
          (Arith.｀ x) _ →
            ` x
          (Arith.∥ s ∥) ⊆as →
            ∣ var $ raise ς $ index $ ⊆as 0 ∣ `- ` (+ η)
          (x Arith.`+ y) ⊆as →
               Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
            `+ Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
          (x Arith.`- y) ⊆as →
               Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
            `- Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})

        Bᵖʳ : (e : Predicate) → secrets e ⊆ as → Script (ς + m) `Bool
        Bᵖʳ = λ where
          Predicate.`true _ →
            `true
          (p Predicate.`∧ q) ⊆as →
               Bᵖʳ p (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names p} {names q})
            `∧ Bᵖʳ q (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names p) {names q})
          (Predicate.`¬ p) ⊆as →
            `not (Bᵖʳ p ⊆as)
          (x Predicate.`= y) ⊆as →
               Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
            `= Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})
          (x Predicate.`< y) ⊆as →
               Bᵃʳ x (⊆as ∘ ∈-mapMaybe-++⁺ˡ isInj₁ {names x} {names y})
            `< Bᵃʳ y (⊆as ∘ ∈-mapMaybe-++⁺ʳ isInj₁ (names x) {names y})

    ... | _
        = ς , versig (mapWith∈ partG $ K² D∈) (allFin ς)

    Tᵢₙᵢₜ : Tx (length xs) 1
    Tᵢₙᵢₜ = sig⋆ (fromList∘mapWith∈ xs K⋆)
      record
      { inputs  = fromList∘mapWith∈ xs (hashTxⁱ ∘ txout₀ ∘ xs⊆)
      ; wit     = wit⊥
      ; relLock = replicate 0
      ; outputs = [ -, v₀ locked-by ƛ ⋁ (mapWith∈ C₀ $ Bₒᵤₜ ∘ subterms⊆ᶜ) .proj₂ ]
      ; absLock = 0 }
      where
        xs⊆ : xs ⊆ ids G₀
        xs⊆ = persistentIds⊆ {G₀}

        K⋆ : xs ↦ List KeyPair
        K⋆ = [_] ∘ K ∘ proj₂ ∘ part₀ ∘ xs⊆

    Tᵢₙᵢₜ♯ = (∃Tx ∋ -, -, Tᵢₙᵢₜ) ♯

    infix 0 _&_&_&_&_&_&_&_&_&_&_
    record State (c : ℂ) : Type where
      constructor _&_&_&_&_&_&_&_&_&_&_
      pattern
      field
        T,o  : TxInput
        curV : Value
        P    : ∃ (_⊆ partG)
        curT : Time

        p⊆ : participants c ⊆ partG
        s⊆ : subterms c ⊆ subterms C₀
        ∃s : case c of λ{ (ℂ.D _) → ∃ (_∈ subterms C₀) ; _ → ⊤}

        sechash : Sechash c
        txout   : Txout c
        part    : ids c ↦ ∃ (_∈ partG)
        val     : ids c ↦ Value
    open State

    Return : ℂ → Type
    Return c = subterms⁺ c ↦′ BranchTx

    go : ∀ c → (∀ c′ → c′ ≺ c → State c′ → Return c′) → State c → Return c
    go (ℂ.D c) r
       (T,o & v & P , P⊆ & t & p⊆ & s⊆ & ∃s@(Dₚ , Dₚ∈) & sechash & txout & part & val)
      with c
    -- Bd
    ... | withdraw A = λ where
      (here refl) →
       sig⋆ [ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
         { inputs  = [ T,o ]
         ; wit     = wit⊥
         ; relLock = [ 0 ]
         ; outputs = [ 1 , v locked-by ƛ versig [ K {A} (p⊆ 0) ] [ 0 ] ]
         ; absLock = t }
    ... | A ∶ d = r (ℂ.D d) ≺-auth
      (T,o & v & P \\ [ A ] , P⊆ ∘ \\-⊆ & t & p⊆ ∘ there
           & s⊆ & ∃s & sechash & txout & part & val)
    ... | after t′ ∶ d = r (ℂ.D d) ≺-after
      (T,o & v & (P , P⊆) & t ⊔ t′ & p⊆ & s⊆ & ∃s & sechash & txout & part & val)
    -- Bc
    ... | c@(put zs &reveal as if p ⇒ cs) = λ where
      (here refl) → Tᶜ
      (there x∈)  → r (ℂ.C cs) ≺-put
        ( (Tᶜ♯ at 0) & v′ & (partG , ⊆-refl) & 0
        & p⊆ & s⊆ & tt
        & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
        & part    ∘ mapMaybe-⊆ isInj₂ n⊆ & val   ∘ mapMaybe-⊆ isInj₂ n⊆
        ) x∈
       where
        n⊆ : names cs ⊆ names c
        n⊆ = ∈-++⁺ʳ (inj₂ <$> zs) ∘ ∈-++⁺ʳ (inj₁ <$> as)

        cs⊆ : cs ⊆ subterms C₀
        cs⊆ = s⊆ ∘ subterms⊆ᶜ

        zs⊆ : zs ⊆ ids c
        zs⊆ = (λ x∈ → ∈-mapMaybe⁺ isInj₂ x∈ refl) ∘ ∈-++⁺ˡ ∘ ∈-map⁺ inj₂

        v′ = v + sum (mapWith∈ zs $ val ∘ zs⊆)

        K⋆ : zs ↦ List KeyPair
        K⋆ = [_] ∘ K ∘ proj₂ ∘ part ∘ zs⊆

        Tᶜ : BranchTx c
        Tᶜ = sig⋆ (mapWith∈ P (K² Dₚ∈ ∘ P⊆) ∷ fromList∘mapWith∈ zs K⋆)
          record
          { inputs  = T,o ∷ fromList∘mapWith∈ zs (hashTxⁱ ∘ txout ∘ zs⊆)
          ; wit     = wit⊥
          ; relLock = replicate 0
          ; outputs = [ _ , v′ locked-by ƛ ⋁ (mapWith∈ cs $ Bₒᵤₜ ∘ cs⊆) .proj₂ ]
          ; absLock = t }
        Tᶜ♯ = (∃Tx ∋ -, -, Tᶜ) ♯
    -- Bpar
    ... | c@(split vcs) = λ where
      (here refl) → Tᶜ
      (there x∈)  → r (ℂ.V vcs) ≺-split
        ( (Tᶜ♯ at 0) & v & (partG , ⊆-refl) & 0
        & p⊆ & s⊆ & tt
        & sechash & txout & part & val
        ) x∈
       where
        Tᶜ : BranchTx c
        Tᶜ = sig⋆ [ mapWith∈ P (K² Dₚ∈ ∘ P⊆) ] record
          { inputs  = [ T,o ]
          ; wit     = wit⊥
          ; relLock = replicate 0
          ; outputs = mapWith∈ (fromList vcs) λ{ {vᵢ , Cᵢ} x∈ →
              let eᵢ = mapWith∈ Cᵢ $ Bₒᵤₜ ∘ s⊆ ∘ subterms⊆ᵛ (fromList⁻ x∈)
              in -, vᵢ locked-by ƛ proj₂ (⋁ eᵢ)
            }
          ; absLock = t }
        Tᶜ♯ = (∃Tx ∋ -, -, Tᶜ) ♯

    go (ℂ.C _) r st = ↦-∈ λ {d} d∈ → r (ℂ.D d) (≺-∈ d∈) (↓ st d∈)
      where
        ↓ : State (ℂ.C ds) → ds ↦′ (State ∘ ℂ.D)
        ↓ {ds = d ∷ ds}
          (T,o & v & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val)
          (here refl)
          = T,o & v & P⊆ & t & p⊆ ∘ ∈-++⁺ˡ & s⊆′ & (d , s⊆ 0)
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part    ∘ mapMaybe-⊆ isInj₂ n⊆ & val   ∘ mapMaybe-⊆ isInj₂ n⊆
          where
            n⊆ : names d ⊆ names (d ∷ ds)
            n⊆ = ∈-++⁺ˡ

            s⊆′ : subterms d ⊆ subterms C₀
            s⊆′ = s⊆ ∘ there ∘ ∈-++⁺ˡ
        ↓ {ds = d ∷ ds}
          (T,o & v & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val)
          (there x∈)
          = ↓ {ds = ds} (T,o & v & P⊆ & t
          & p⊆ ∘ (∈-++⁺ʳ _) & s⊆ ∘ ∈-++⁺ʳ _ & tt
          & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
          & part    ∘ mapMaybe-⊆ isInj₂ n⊆ & val   ∘ mapMaybe-⊆ isInj₂ n⊆) x∈
          where n⊆ : names ds ⊆ names (d ∷ ds)
                n⊆ = ∈-++⁺ʳ _
    go (ℂ.V _) r st = ↦-∈ᵛ λ {c} c∈ → r (ℂ.C c) (≺-∈ᵛ c∈) (↓ᵛ st c∈)
      where
        ↓ᵛ : State (ℂ.V vcs) → (proj₂ <$> vcs) ↦′ (State ∘ ℂ.C)
        ↓ᵛ {vcs = (v , c) ∷ vcs}
           (T,o & _ & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val)
           (here refl)
           = T,o & v & P⊆ & t & p⊆ ∘ ∈-++⁺ˡ & s⊆ ∘ ∈-++⁺ˡ & tt
           & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
           & part    ∘ mapMaybe-⊆ isInj₂ n⊆ & val   ∘ mapMaybe-⊆ isInj₂ n⊆
           where n⊆ : names c ⊆ names ((v , c) ∷ vcs)
                 n⊆ = ∈-++⁺ˡ
        ↓ᵛ {vcs = (v , c) ∷ vcs}
           ((T at o) & _ & P⊆ & t & p⊆ & s⊆ & tt & sechash & txout & part & val)
           (there x∈)
           = ↓ᵛ {vcs = vcs} ((T at suc o) & v & P⊆ & t
           & p⊆ ∘ ∈-++⁺ʳ _ & s⊆ ∘ ∈-++⁺ʳ _ & tt
           & sechash ∘ mapMaybe-⊆ isInj₁ n⊆ & txout ∘ mapMaybe-⊆ isInj₂ n⊆
           & part    ∘ mapMaybe-⊆ isInj₂ n⊆ & val   ∘ mapMaybe-⊆ isInj₂ n⊆) x∈
           where n⊆ : names vcs ⊆ names ((v , c) ∷ vcs)
                 n⊆ = ∈-++⁺ʳ _
