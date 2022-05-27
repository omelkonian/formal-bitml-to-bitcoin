open import Prelude.Init hiding (T)
open L.Mem
open import Prelude.Lists
open import Prelude.General
open import Prelude.DecLists
open import Prelude.DecEq

open import Prelude.Collections
open import Prelude.Monoid

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Ord
open import Prelude.ToN
open import Prelude.Validity
open import Prelude.Traces
open import Prelude.Setoid
open import Prelude.Nary
open import Prelude.Apartness

open import Bitcoin.Crypto using (KeyPair)

module SecureCompilation.Coherence
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)

  (finPart : Finite Participant)
  (keypairs : ∀ (A : Participant) → KeyPair × KeyPair)

  (η : ℕ) -- security parameter
  where

open import SymbolicModel Participant Honest as S
  hiding (_∎; begin_; d)

open import ComputationalModel Participant Honest finPart keypairs as C
  hiding (Hon; Initial; Σ
         ; t; t′; `; ∣_∣; n)

open import SecureCompilation.Compiler Participant Honest η

private
  variable
    ⟨G⟩C ⟨G⟩C′ ⟨G⟩C″ : Ad
    T T′ : ∃Tx

    𝕣  : ℝ Rˢ
    ∃𝕣 ∃𝕣′ : ∃ ℝ

postulate
  encode : Txout Rˢ → Ad → Message
  -- ^ encode {G}C as a bitstring, representing each x in it as txout(x)

  SIGᵖ : ∀ {A : Set} → ℤ {- public key -} → A → ℤ

  ∣_∣ᶻ : ℤ → ℕ
  ∣_∣ᵐ : Message → ℕ

_-redeemableWith-_ : S.Value → KeyPair → ∃TxOutput
v -redeemableWith- k = Ctx 1 , record {value = v;  validator = ƛ (versig [ k ] [ # 0 ])}

-- T0D0: redefine Message ≈ ℤ ??
SIGᵐ : KeyPair → Message → Message
SIGᵐ k = map (SIG k)

-- Convenient wrapper for calling the BitML compiler.
COMPILE : 𝔾 ad → ∃Tx¹ × (subtermsᵃ′ ad ↦′ ∃Txᶜ ∘ removeTopDecorations)
COMPILE {ad = ad} (vad , txout₀ , sechash₀ , κ₀) =
  let
    K : 𝕂 (ad .G)
    K {p} _ = K̂ p

    T , ∀d = bitml-compiler {ad = ad} vad sechash₀ txout₀ K κ₀
  in
    T , (∀d ∘ h-subᶜ {ds = ad .C})

-- Convenient extensions of symbolic/computational runs.
record ℝˢ : Set where
  constructor _⦊_
  field run : S.Run
        {cfg} : Cfgᵗ
        label : 𝕃 run cfg
record ℝᶜ : Set where
  constructor _⦊_
  field run   : C.Run
        label : C.Label
infix 3 _⦊_

ℝˢ⇒ℝ : (𝕣ˢ : ℝˢ) → let open ℝˢ 𝕣ˢ in ℝ (_ ∷ run ⊣ label .proj₁)
ℝˢ⇒ℝ (_ ⦊ _ , 𝕣) = 𝕣

txout∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ Txout ⦆ Rˢ
txout∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) txout′ =
  destruct≡-++/↦ {zs = namesʳ (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (namesʳ-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    txout′ .proj₁

sechash∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ Sechash ⦆ Rˢ
sechash∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) sechash′ =
  destruct≡-++/↦ {zs = namesˡ (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (namesˡ-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    sechash′ .proj₁

κ∷˘ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) →
  (Γₜ ∷ Rˢ ⊣ 𝕒) →⦅ 𝕂² ⦆ Rˢ
κ∷˘ {Rˢ = Rˢ} {Γₜ = Γₜ} 𝕒@(_ , _ , _ , Γ→ , eq) κ′ =
  destruct≡-++/↦ {zs = advertisements (Γₜ ∷ Rˢ ⊣ 𝕒)}
    (ads-←—— {Γₜ = Γₜ} {R = Rˢ} Γ→ eq)
    κ′ .proj₁

drop-ℝ : ∀ (𝕒 : 𝔸 Rˢ Γₜ) → ℝ (Γₜ ∷ Rˢ ⊣ 𝕒) → ℝ Rˢ
drop-ℝ {Rˢ = Rˢ} 𝕒 𝕣′ =
  [txout:   txout∷˘   {Rˢ = Rˢ} 𝕒 txout′
  ∣sechash: sechash∷˘ {Rˢ = Rˢ} 𝕒 sechash′
  ∣κ:       κ∷˘       {Rˢ = Rˢ} 𝕒 κ′
  ] where open ℝ 𝕣′

𝕃⇒ℝ : 𝕃 Rˢ Γₜ → ℝ Rˢ
𝕃⇒ℝ (𝕒 , 𝕣′) = drop-ℝ 𝕒 𝕣′

-- * Inductive case 1

data _~₁₁_ : ℝˢ → ℝᶜ → Set where

  -- ** Stipulation: advertisting a contract
  [1] : ∀ {𝕣 : ℝ Rˢ} →
      let
        open ℝ 𝕣
        ⟨ G ⟩ C = ⟨G⟩C ; partG = nub-participants G
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = advertise⦅ ⟨G⟩C ⦆
        Γ′  = ` ⟨G⟩C ∣ Γ
        t′  = t
        Γₜ′ = Γ′ at t′

        C  = encode {Rˢ} txout′ ⟨G⟩C
        λᶜ = A →∗∶ C
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [C-Advertise]
      (vad : Valid ⟨G⟩C)
      (hon : Any (_∈ Hon) partG)
      (d⊆  : ⟨G⟩C ⊆⦅ deposits ⦆ Γ)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-Advertise] vad hon d⊆) refl

        -- txout′ = txout, sechash′ = sechash, κ′ = κ
        open H₁ 𝕣 t α t′ Γ R≈ ⟨G⟩C Γ→Γ′ ∃Γ≈
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

{-
  -- ** Stipulation: committing secrets
  [2] : ∀ {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
        ∀ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C}

    → let
        ⟨ G ⟩ C = ⟨G⟩C
        Γ = ` ⟨G⟩C ∣ Γ₀
        Γₜ = Γ at t
      in
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        C : Message
        C = encode {Rˢ} txout′ ⟨G⟩C

        Δ : List (Secret × Maybe ℕ)
        Δ = map (λ{ (s , mn , _) → s , mn }) Δ×h̅

        -- [BUG] leads to internal error
        -- (unsolved meta after serialization, c.f. issue #5584)
        -- (as , ms) = unzip Δ
        as = proj₁ $ unzip Δ
        ms = proj₂ $ unzip Δ

        Δᶜ : Cfg
        Δᶜ = || map (uncurry ⟨ A ∶_♯_⟩) Δ

        h̅ : List ℤ -- ≈ Message
        h̅ = map (proj₂ ∘ proj₂) Δ×h̅

        k̅ : List ℤ -- ≈ Message
        k̅ = concatMap (map pub ∘ codom) (codom k⃗)

        C,h̅,k̅ : Message
        C,h̅,k̅ = C ◇ h̅ ◇ k̅

        C,h̅,k̅ₐ : Message
        C,h̅,k̅ₐ = SIGᵐ (K A) C,h̅,k̅

        α   = auth-commit⦅ A , ⟨G⟩C , Δ ⦆
        Γ′  = Γ ∣ Δᶜ ∣ A auth[ ♯▷ ⟨G⟩C ]
        t′  = t
        Γₜ′ = Γ′ at t′
        λᶜ  = B →∗∶ C,h̅,k̅ₐ
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [C-AuthCommit]
      (as≡ : as ≡ secretsOfᵖ A G)
      (All∉ : All (_∉ secretsOfᶜᶠ A Γ₀) as)
      (Hon⇒ : A ∈ Hon → All Is-just ms)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthCommit] as≡ All∉ Hon⇒) refl

        -- (v) txout = txout′ (vi) extend sechash′ (vii) extend κ′
        sechash⁺ : as ↦ ℤ
        sechash⁺ a∈ =
          let _ , a×m∈ , _    = ∈-unzip⁻ˡ Δ a∈
              (_ , _ , z) , _ = ∈-map⁻ (λ{ (s , mn , _) → s , mn }) a×m∈
          in z

        open H₂ {Rˢ} 𝕣 t α t′ Γ R≈ A A ⟨G⟩C Δ sechash⁺ k⃗ Γ→Γ′ ∃Γ≈
      in
      -- (i) ⟨G⟩C has been previously advertised in Rᶜ
      -- T0D0: make sure it is the first occurrence of such a broadcast in Rᶜ
      (∃ λ B → (B →∗∶ C) ∈ Rᶜ)

      -- (ii) broadcast message in Rᶜ
      -- T0D0: make sure that λᶜ is the first occurrence of such a message after C in Rᶜ
    -- → ∃ λ B → λᶜ ≡ B →∗∶ C,h̅,k̅ₐ
    → All (λ hᵢ → ∣ hᵢ ∣ᶻ ≡ η) h̅

      -- (iii) each hᵢ is obtained by querying the oracle, otherwise we have a dishonestly chosen secret
    → All (λ{ (_ , just Nᵢ , hᵢ)
            → ∃ λ B → ∃ λ mᵢ → ((B , mᵢ , [ hᵢ ]) ∈ oracleInteractions Rᶜ) × (∣ mᵢ ∣ᵐ ≡ η + Nᵢ)
            ; (_ , nothing , hᵢ)
            → [ hᵢ ] ∉ map (proj₂ ∘ proj₂) (filter ((η ≤?_) ∘ ∣_∣ᵐ ∘ proj₁ ∘ proj₂) (oracleInteractions Rᶜ))
            }) Δ×h̅

      -- (iv) no hash is reused
    → Unique h̅
    → Disjoint h̅ (codom sechash′)
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Stipulation: authorizing deposits
  [3] : let ⟨ G ⟩ C = ⟨G⟩C ; partG = G ∙partG in
        let Γ = ` ⟨G⟩C ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-init⦅ A , ⟨G⟩C , x ⦆
        Γ′  = Γ ∣ A auth[ x ▷ˢ ⟨G⟩C ]
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [C-AuthInit]
      (committedA : partG ⊆ committedParticipants ⟨G⟩C Γ₀)
      (A∈per : (A , v , x) ∈ persistentDeposits G)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthInit] committedA A∈per) refl

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        open H₃ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ A x R≈ Γ→Γ′ ∃Γ≈

        -- invoke compiler
        T : ∃Tx
        T = let (_ , Tᵢₙᵢₜ) , _ = COMPILE (Liftᶜ committedA)
            in -, -, Tᵢₙᵢₜ

        -- (i) broadcast Tᵢₙᵢₜ , signed with A's private key
        m = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m

      in
      -- (ii) Tᵢₙᵢₜ occurs as a message in Rᶜ
      (∃ λ B → (B →∗∶ [ T ♯ ]) ∈ Rᶜ)

      -- (iii) broadcast message in Rᶜ
      -- T0D0: make sure that λᶜ is the first occurrence of such a message after Tinit in Rᶜ
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Stipulation: activating the contract
  [4] :
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
      -- (i) consume {G}C and its persistent deposits from Rˢ
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = init⦅ G , C ⦆
        Γ′  = ⟨ C , v ⟩at z ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [C-Init]
      (fresh-z : z ∉ xs ++ ids Γ₀) →
      let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-Init] fresh-z) refl

        open H₄ {Rˢ} 𝕣 t α t′ ⟨G⟩C Γ₀ toSpend v z R≈ Γ→Γ′ ∃Γ≈

        -- invoke compiler
        T : ∃Tx
        T = let (_ , Tᵢₙᵢₜ) , _ = COMPILE Liftᶜ
            in -, -, Tᵢₙᵢₜ

        -- (ii) append Tᵢₙᵢₜ to the blockchain
        λᶜ = submit T

        -- (iii) sechash = sechash′, κ = κ′, txout extends txout′ with (z ↦ Tᵢₙᵢₜ)
        open H₄′ (T at 0F)
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Contract actions: authorize control
  [5] : ∀ {i : Index c} → let open ℝ 𝕣; open ∣SELECT c i in
        let Γ = ⟨ c , v ⟩at x ∣ Γ₀; Γₜ = Γ at t in
        ∀ {A} → -- [T0D0] fixed in Agda-HEAD, see issue #5683

      -- D ≡ A ∶ D′
      (D≡A:D′ : A ∈ authDecorations d)
      -- (i) Rˢ contains ⟨C , v⟩ₓ with C = D + ∑ᵢ Dᵢ
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-control⦅ A , x ▷ d ⦆
        Γ′  = ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [C-AuthControl], already in hypothesis `D≡A:D′`
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([C-AuthControl] D≡A:D′) refl

        -- (iv) txout = txout′, sechash = sechash′, κ = κ′
        open H₅ {Rˢ} 𝕣 t α t′ c v x Γ₀ A i R≈ Γ→Γ′ ∃Γ≈

        -- (ii) {G}C is the ancestor of ⟨C, v⟩ₓ in Rˢ
        ⟨G⟩C , vad , ad∈ , c⊆ , anc = ANCESTOR {R = Rˢ} {Γ = Γ} R≈ (here refl)
        ⟨ G ⟩ C = ⟨G⟩C; partG = G ∙partG

        d∈ : d ∈ subtermsᵃ′ ⟨G⟩C
        d∈ = c⊆ (L.Mem.∈-lookup i)

        A∈ : A ∈ partG
        A∈ = ∈-nub⁺ $ subterms′-part⊆ᵃ vad d∈ $ auth⊆part {d = d} D≡A:D′

        T : ∃Tx
        T = let _ , ∀d∗ = COMPILE (Liftᶜ anc)
                _ , Tᵈ = ∀d∗ d∈
            in -, -, Tᵈ

        λᶜ = B →∗∶ [ SIGᵖ (κ′ ad∈ d∈ {A} A∈ .pub) T ]
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Contract actions: put
  [6] : ∀ {ds : List (Participant × S.Value × Id)} {ss : List (Participant × Secret × ℕ)} →
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
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
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

        open H₆ {Rˢ} 𝕣 t α t′ c v y ds Γ₂ c′ y′ R≈ Γ→Γ′ ∃Γ≈

        -- (iii) {G}C″ is the ancestor of ⟨D+C, v⟩y in Rˢ
        ⟨G⟩C″ , _ , _ , c⊆ , anc = ANCESTOR {R = Rˢ} {Γ = Γ} R≈ (here refl)
        ⟨ G ⟩ C″ = ⟨G⟩C″

        d∈ : d ∈ subtermsᵃ′ ⟨G⟩C″
        d∈ = c⊆ (L.Mem.∈-lookup i)

        -- (iv) submit transaction T
        --      where ∙ (T′,o) = txout′(y)
        --            ∙ T is the first transaction in Bc(c′,d,T′,o,v′,x⃗,partG,t)
        --      i.e. the one corresponding to subterm `d∗ = put xs &reveal as if p → c′`
        T : ∃Tx
        T = let _ , ∀d∗ = COMPILE (Liftᶜ anc)
                _ , Tᵈ = ∀d∗ d∈ :~ d≡ ⟪ ∃Txᶜ ⟫
            in -, -, Tᵈ

        λᶜ = submit T

        -- (v) extend txout′ with {y′↦(T,0)}, sechash = sechash′, κ = κ′
        open H₆′ (T at 0F)
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Contract actions: authorize reveal
  [7] : ∀ {a} → -- [T0D0] fixed in Agda-HEAD, see issue #5683
        ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣; Γ = ⟨ A ∶ a ♯ just n ⟩ ∣ Γ₀; Γₜ = Γ at t in
        ∀ {Δ×h̅ : List (Secret × Maybe ℕ × ℤ)} {k⃗ : 𝕂²′ ⟨G⟩C} → let ⟨ G ⟩ C = ⟨G⟩C in

      ∣ m ∣ᵐ ≤ η
    → (R≈ : Rˢ ≈⋯ Γₜ)

    → let
        α   = auth-rev⦅ A , a ⦆
        Γ′  = A ∶ a ♯ n ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [C-AuthRev] refl

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

        -- T0D0: should we search for a signature of this message instead?
        C,h̅,k̅ : Message
        C,h̅,k̅ = C ◇ h̅ ◇ k̅

        -- (i) some participant B broadcasts message m
        λᶜ = B →∗∶ m

        -- (iii) txout = txout′, sechash = sechash′, κ = κ′
        open H₇ 𝕣 t α t′ A a n Γ₀ R≈ Γ→Γ′ ∃Γ≈
      in
      -- (ii) in Rᶜ we find ⋯ (B → O ∶ m) (O → B : sechash′(a)) for some B ⋯
      (∃ λ B → (B , m , [ sechash′ {a} a∈ ]) ∈ oracleInteractions Rᶜ)

      -- (iv) in Rˢ, we find an A:{G}C,∆ action, with a in G
    → (∃α : auth-commit⦅ A , ⟨G⟩C , Δ ⦆ ∈ labels Rˢ)
    → a ∈ namesˡ G

      -- ... with a corresponding broadcast of m′=(C,h̅,k̅) in Rᶜ
    → (∃λ : Any (λ l → ∃ λ B → l ≡ B →∗∶ C,h̅,k̅) Rᶜ)

      -- (v) λᶜ is the first broadcast of m after the first broadcast of m′
    → All (λ l → ∀ X → l ≢ X →∗∶ m) (Any-tail ∃λ)
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Contract actions: split
  [8] : ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in
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
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
    → let
        ∀≤t : All (_≤ t′) ts
        ∀≤t = ⟪ (λ ◆ → All (_≤ ◆) ts) ⟫ t≡ ~: ∀≤max t ts

        split→ : ⟨ [ d∗ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′
        split→ = ⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡
              ~: [C-Split] {vcis = vcis} fresh-xs

        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Timeout] As≡∅ ∀≤t split→ refl

        open H₈ {Rˢ} 𝕣 t α t′ c v y Γ₀ vcis R≈ Γ→Γ′ ∃Γ≈

        -- (iii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
        ⟨G⟩C′ , _ , _ , c⊆ , anc = ANCESTOR {R = Rˢ} {Γ = Γ} R≈ (here refl)
        ⟨ G ⟩ C′ = ⟨G⟩C′

        d∈ : d ∈ subtermsᵃ′ ⟨G⟩C′
        d∈ = c⊆ (L.Mem.∈-lookup i)

        -- (iii) submit transaction T
        --       where ∙ (T′,o) = txout′(y)
        --             ∙ T is the first transaction in Bpar(cs,d,T′,o,partG,t)
        --       i.e. the one corresponding to subterm `d∗ = split (zip vs cs)`
        T =
          let
            _ , ∀d∗ = COMPILE (Liftᶜ anc)
            i , Tᵈ = ∀d∗ d∈ :~ d≡ ⟪ ∃Txᶜ ⟫

            open ≡-Reasoning renaming (_∎ to _∎∎)
            vs≡ , cs≡ , xs≡ = length-unzip₃ vcis

            l≡ : length xs ≡ length (zip vs cs)
            l≡ = sym
               $ begin length (zip vs cs)    ≡⟨ L.length-zipWith _,_ vs cs ⟩
                       length vs ⊓ length cs ≡⟨ Nat.m≥n⇒m⊓n≡n $ Nat.≤-reflexive $ trans cs≡ (sym vs≡) ⟩
                       length cs             ≡⟨ cs≡ ⟩
                       length vcis           ≡⟨ sym xs≡ ⟩
                       length xs             ∎∎

            Tᵈ′ : Tx i (length xs)
            Tᵈ′ = ⟪ Tx i ⟫ l≡ ~: Tᵈ
          in -, -, Tᵈ′

        λᶜ = submit T

        -- (iv) extend txout′ with {xᵢ ↦ (T,i)}, sechash = sechash′, κ = κ′
        txout⁺ : xs ↦ TxInput′
        txout⁺ x∈ = T at (L.Any.index x∈)

        open H₈′ txout⁺
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Contract actions: withdraw
  [9] : ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in
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
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [C-Withdraw]
      (fresh-x : x ∉ y L.∷ ids Γ₀)
      -- Hypotheses from [Timeout]
      (As≡∅ : Null As)
      (∀≤t : All (_≤ t) ts)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Timeout] As≡∅ ∀≤t (⟪ (λ ◆ → ⟨ [ ◆ ] , v ⟩at y ∣ Γ₀ —[ α ]→ Γ′) ⟫ d≡ ~: [C-Withdraw] fresh-x) refl

        open H₉ {Rˢ} 𝕣 t α t′ c v y Γ₀ A x R≈ Γ→Γ′ ∃Γ≈

        -- (ii) {G}C′ is the ancestor of ⟨D+C,v⟩y in Rˢ
        ⟨G⟩C′ , _ , _ , c⊆ , anc = ANCESTOR {R = Rˢ} {Γ = Γ} R≈ (here refl)
        ⟨ G ⟩ C′ = ⟨G⟩C′

        d∈ : d ∈ subtermsᵃ′ ⟨G⟩C′
        d∈ = c⊆ (L.Mem.∈-lookup i)

        --   ∙ T′ at o = txout′(x)
        --   ∙ T is the first transaction of Bd(d,d,T′,o,v,partG,0)
        -- i.e.
        -- (iii) submit transaction T
        --       where ∙ (T′,o) = txout′(y)
        --             ∙ T is the first transaction in Bd(d,d,T′,o,v,partG,0)
        --       i.e. the one corresponding to subterm `d∗ = withdraw A`
        T = let _ , ∀d∗ = COMPILE (Liftᶜ anc)
                _ , Tᵈ = ∀d∗ d∈ :~ d≡ ⟪ ∃Txᶜ ⟫
            in -, -, Tᵈ

        λᶜ = submit T

        -- (iv) extend txout′ with {x ↦ (T,0)}, sechash = sechash′, κ = κ′
        open H₉′ (T at 0F)
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: authorize join
  [10] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
          let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-join⦅ A , x ↔ x′ ⦆
        Γ′  = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-AuthJoin] refl

        n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
        x∈  = n⊆ (here refl)
        x∈′ = n⊆ (there $′ here refl)
      in
      (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                → (l ≡ B →∗∶ [ T ♯ ])
                × (inputs  T ≡ hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ [])
                × (outputs T ≡ V.[ Ctx 1 , record {value = v + v′; validator = ƛ (versig [ K̂ A ] [ # 0 ])} ])
                ) Rᶜ)
    → let
        T : ∃Tx
        T = 2 , 1 , (L.Any.satisfied ∃λ .proj₂ .proj₂ .proj₁)

        -- (iii) broadcast transaction T, signed by A
        m′ = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₀ {Rˢ} 𝕣 t α t′ A v x v′ x′ Γ₀ R≈ Γ→Γ′ ∃Γ≈
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: join
  [11] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
          let Γ = ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at x′ ∣ A auth[ x ↔ x′ ▷⟨ A , v + v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = join⦅ x ↔ x′ ⦆
        Γ′  = ⟨ A has (v + v′) ⟩at y ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [DEP-Join]
      (fresh-y : y ∉ x L.∷ x′ ∷ ids Γ₀)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-Join] fresh-y) refl

        n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
        x∈  = n⊆ (here refl)
        x∈′ = n⊆ (there $′ here refl)

        -- (ii) submit transaction T
        T : ∃Tx
        T  = 2 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = hashTxⁱ (txout′ {x} x∈) ∷ hashTxⁱ (txout′ {x′} x∈′) ∷ []
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.[ (v + v′) -redeemableWith- K̂ A ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (iii) extend txout′ with y↦T₀ (removing {x↦_;x′↦_}), sechash = sechash′, κ = κ′
        open H₁₁ {Rˢ} 𝕣 t α t′ A v x v′ x′ y Γ₀ R≈ (T at 0F) Γ→Γ′ ∃Γ≈
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: authorize divide (similar to [10])
  [12] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
          let Γ = ⟨ A has (v + v′) ⟩at x ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-divide⦅ A , x ▷ v , v′ ⦆
        Γ′  = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-AuthDivide] refl

        n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
        x∈  = n⊆ (here refl)
      in
      (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                → (l ≡ B →∗∶ [ T ♯ ])
                × (inputs  T ≡ V.[ hashTxⁱ (txout′ {x} x∈) ])
                × (outputs T ≡ (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ [])
                ) Rᶜ)
    → let
        T : ∃Tx
        T = 1 , 2 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

        -- (iii) broadcast transaction T, signed by A
        m′ = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₂ {Rˢ} 𝕣 t α t′ A v v′ x Γ₀ R≈ Γ→Γ′ ∃Γ≈
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: divide (dimilar to [11])
  [13] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
          let Γ = ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = divide⦅ x ▷ v , v′ ⦆
        Γ′  = ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [DEP-Divide]
      (fresh-ys : All (_∉ x L.∷ ids Γ₀ ) (y ∷ y′ ∷ []))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-Divide] fresh-ys) refl

        n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
        x∈  = n⊆ (here refl)

        -- (iii) submit transaction T
        T  = 1 , 2 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = V.[ hashTxⁱ (txout′ {x} x∈) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = (v -redeemableWith- K̂ A) ∷ (v′ -redeemableWith- K̂ A) ∷ []
          ; absLock = 0 }
        λᶜ = submit T

        -- (v) extend txout′ with {y↦T₀, y′↦T₁} (removing x↦T₀), sechash = sechash′, κ = κ′
        open H₁₃ {Rˢ} 𝕣 t α t′ A v v′ x Γ₀ y y′ R≈ (T at 0F) (T at 1F) Γ→Γ′ ∃Γ≈
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: authorize donate (similar to [10])
  [14] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
          let Γ = ⟨ A has v ⟩at x ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-donate⦅ A , x ▷ᵈ B′ ⦆
        Γ′  = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-AuthDonate] refl

        n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
        x∈  = n⊆ (here refl)
      in
      (∃λ : Any (λ l → ∃ λ B → ∃ λ T
                → (l ≡ B →∗∶ [ T ♯ ])
                × (inputs  T ≡ V.[ hashTxⁱ (txout′ {x} x∈) ])
                × (outputs T ≡ V.[ v -redeemableWith- K̂ B′ ])
                ) Rᶜ)
    → let
        T : ∃Tx
        T = 1 , 1 , (proj₁ $ proj₂ $ proj₂ $ L.Any.satisfied ∃λ)

        -- (iii) broadcast transaction T, signed by A
        m′ = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m′

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₄ {Rˢ} 𝕣 t α t′ A v x Γ₀ B′ R≈ Γ→Γ′ ∃Γ≈
      in
      -- (iv) λᶜ is the first broadcast of m′ in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m′) (Any-tail ∃λ)
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: donate (similar to [11])
  [15] : ∀ {Rˢ} {𝕣 : ℝ Rˢ} → let open ℝ 𝕣 in
          let Γ = ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B′ ] ∣ Γ₀; Γₜ = Γ at t in

      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = donate⦅ x ▷ᵈ B′ ⦆
        Γ′  = ⟨ B′ has v ⟩at y ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [DEP-Donate]
      (fresh-y : y ∉ x L.∷ ids Γ₀)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-Donate] fresh-y) refl

        n⊆ : Γ ⊆⦅ namesʳ ⦆ Rˢ
        n⊆  = namesʳ⦅end⦆⊆ Rˢ ∘ ∈namesʳ-resp-≈ _ {Γ}{cfg (Rˢ .end)} (↭-sym $ proj₂ R≈)
        x∈  = n⊆ (here refl)

        -- (iii) submit transaction T
        T  = 1 , 1 , sig⋆ (V.replicate [ K̂ A ]) record
          { inputs  = V.[ hashTxⁱ (txout′ {x} x∈) ]
          ; wit     = wit⊥
          ; relLock = V.replicate 0
          ; outputs = V.[ v -redeemableWith- K̂ B′ ]
          ; absLock = 0 }
        λᶜ = submit T

        -- (v) extend txout′ with y↦T₀ (removing x↦T₀), sechash = sechash′, κ = κ′
        open H₁₅ {Rˢ} 𝕣 t α t′ A v x B′ Γ₀ y R≈ (T at 0F) Γ→Γ′ ∃Γ≈
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)

  -- ** After
  [18] :

      (δ>0 : δ > 0)
    → let
        Γₜ@(Γ at t) = Rˢ .end
        α   = delay⦅ δ ⦆
        t′  = t + δ
        Γₜ′ = Γ at t′
        λᶜ  = delay δ
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Delay] δ>0

        open H₁₈ {Rˢ} 𝕣 t α t′ Γ (≈ᵗ-refl {Γₜ}) Γ→Γ′ ∃Γ≈
      in
      --——————————————————————————————————————————————————————————————————————
      (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)
-}
_≁₁₁_ = ¬_ ∘₂ _~₁₁_

data _~₁₂_ : ℝˢ → ℝᶜ → Set where
{-
  -- ** Deposits: authorize destroy
  [16] : ∀ {ds : List (Participant × S.Value × Id)} {j : Index ds}

    → let
        k  = length ds
        xs = map (proj₂ ∘ proj₂) ds
        A  = proj₁ (ds ‼ j)
        j′ = ‼-map {xs = ds} j
        Δ  = || map (λ{ (Bᵢ , vᵢ , xᵢ) → ⟨ Bᵢ has vᵢ ⟩at xᵢ }) ds
        Γ  = Δ ∣ Γ₀
        Γₜ = Γ at t
      in
      -- (ii) in Rˢ we find ⟨Bᵢ,vᵢ⟩yᵢ for i ∈ 1..k
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = auth-destroy⦅ A , xs , j′ ⦆
        Γ′  = Δ ∣ A auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
      -- Hypotheses from [DEP-AuthDestroy]
      (fresh-y : y ∉ ids Γ₀)
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] ([DEP-AuthDestroy] fresh-y) refl

        -- (vii) txout = txout′, sechash = sechash′, κ = κ′
        open H₁₆ {Rˢ} 𝕣 t α t′ ds Γ₀  j A y R≈ Γ→Γ′ ∃Γ≈
      in
      -- (iii) in Rᶜ we find B → ∗ ∶ T, for some T having txout′(yᵢ) as inputs (+ possibly others)
      (T : Tx i 0)
    → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)
    → (T∈ : Any (λ l → ∃ λ B → l ≡ B →∗∶ [ T ♯ ]) Rᶜ)

    → let
        -- (iv) broadcast transaction T, signed by A
        m = [ SIG (K̂ A) T ]
        λᶜ = B →∗∶ m
      in
      -- (v) λᶜ is the first broadcast of m in Rᶜ after the first broadcast of T
      All (λ l → ¬ ∃ λ B → l ≡ B →∗∶ m) (Any-tail T∈)

      -- (vi) λᶜ does not correspond to any *other* symbolic move
    → (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
        → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
        → (Rˢ ⦊ λˢ′) ≁₁₁ (Rᶜ ⦊ λᶜ))
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₂ (Rᶜ ⦊ λᶜ)

  -- ** Deposits: destroy
  [17] : ∀ {ds : List (Participant × S.Value × Id)} {j : Index ds}

    → let
        xs = map (proj₂ ∘ proj₂) ds
        Δ  = || map (λ{ (i , Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                    (enumerate ds)
        Γ  = Δ ∣ Γ₀
        Γₜ = Γ at t
      in
      -- (ii) in Rˢ, α assumes ⟨Aᵢ,vᵢ⟩xᵢ to obtain 0
      (R≈ : Rˢ ≈⋯ Γₜ)
    → let
        α   = destroy⦅ xs ⦆
        Γ′  = Γ₀
        t′  = t
        Γₜ′ = Γ′ at t′
      in
      (∃Γ≈ : ∃ (_≈ᶜ Γ′))
    → let
        Γ→Γ′ : Γₜ —[ α ]→ₜ Γₜ′
        Γ→Γ′ = [Action] [DEP-Destroy] refl

        -- (v) txout = txout′, sechash = sechash′, κ = κ′
        -- remove {⋯ xᵢ ↦ (Tᵢ,j) ⋯} from txout′
        open H₁₇ {Rˢ} 𝕣 t α t′ ds Γ₀ y R≈ Γ→Γ′ ∃Γ≈
      in
      (T : Tx i 0)
    → (hashTxⁱ <$> codom xs↦) ⊆ V.toList (inputs T)

    → let
        -- (iii) submit transaction T
        λᶜ = submit (_ , _ , T)
      in

      -- (iv) λᶜ does not correspond to any *other* symbolic move
      (∀ Γₜ′ (λˢ′ : 𝕃 Rˢ Γₜ′)
        → λˢ′ .proj₁ .proj₁ ≢ λˢ .proj₁ .proj₁
        → (Rˢ ⦊ λˢ′) ≁₁₁ (Rᶜ ⦊ λᶜ))
      --——————————————————————————————————————————————————————————————————————
    → (Rˢ ⦊ λˢ) ~₁₂ (Rᶜ ⦊ λᶜ)
-}
_≁₁₂_ = ¬_ ∘₂ _~₁₂_

data _~₁_ : ℝˢ → ℝᶜ → Set where

  [L]_ : ∀ {λˢ : 𝕃 Rˢ Γₜ}
    → (Rˢ ⦊ λˢ) ~₁₁ (Rᶜ ⦊ λᶜ)
    → (Rˢ ⦊ λˢ) ~₁  (Rᶜ ⦊ λᶜ)

  [R]_ : ∀ {λˢ : 𝕃 Rˢ Γₜ}
    → (Rˢ ⦊ λˢ) ~₁₂ (Rᶜ ⦊ λᶜ)
    → (Rˢ ⦊ λˢ) ~₁  (Rᶜ ⦊ λᶜ)

_≁₁_ = ¬_ ∘₂ _~₁_

-- * Inductive case 2
data _~₂_ (∃Rˢ : ∃ ℝ) : C.Label → Set where
{-
  [1] : let 𝕣 = ∃Rˢ .proj₂; open ℝ 𝕣 in
      T .proj₂ .proj₂ .inputs ♯ (hashTxⁱ <$> codom txout′)
      --————————————————————————————————————————————————————————————
    → ∃Rˢ ~₂ submit T

  [2] :
      (λᶜ ≡ A →O∶ m)
    ⊎ (λᶜ ≡ O→ A ∶ m)
      --——————————————————————————————————————————————————————————————————————
    → ∃Rˢ ~₂ λᶜ

  [3] : let Rˢ = ∃Rˢ .proj₁; λᶜ = A →∗∶ m in
      -- λᶜ does not correspond to any symbolic move
      (∀ {Γₜ Rᶜ} (λˢ : 𝕃 Rˢ Γₜ) → (Rˢ ⦊ λˢ) ≁₁ (Rᶜ ⦊ λᶜ))
      --——————————————————————————————————————————————————————————————————————
    → ∃Rˢ ~₂ λᶜ
-}

data ℂ∗ : C.Run → Set where
  []   : ℂ∗ []
  _∷_ : ℂ∗ Rᶜ → (λᶜ : C.Label) → ℂ∗ (λᶜ ∷ Rᶜ)

data _~~_ : ℝ∗ → ℂ∗ → Set where

data _~′_ : ∃ ℝ → C.Run → Set where

  -- * Base case
{-
  base : let Rˢ , 𝕣 = ∃𝕣; open ℝ 𝕣 in

      -- (i) Rˢ = Γ₀ ∣ 0, with Γ₀ initial
      (init : Initial Γ₀)
    → (R≈ : Rˢ ≡ ((Γ₀ at 0) ∎⊣ (init , refl)))
      -- (ii) Rᶜ = T₀ ⋯ initial
    → (cinit : C.Initial Rᶜ)
    → let ∃T₀ , _ = cinit; _ , o , T₀ = ∃T₀ in

      -- (iii) generation of public keys, we do not consider that here
      -- [T0D0] is our idealistic assumption reasonable?? -- ask BitML authors

      -- (iv) txout { ⟨ A , v ⟩ₓ ∈ Γ₀ ↦ T₀{value = $ v, spendable with K̂(A)(rₐ)} ∈ T₀ }
      (∀ {A v x} (d∈ : ⟨ A has v ⟩at x ∈ᶜ Γ₀)
        → ∃ λ oᵢ
        → let
            x∈ : x ∈ namesʳ Rˢ
            x∈ = ⟪ (λ ◆ → x ∈ namesʳ ◆) ⟫ R≈
              ~: ⟪ (λ ◆ → x ∈ ◆) ⟫ (namesʳ-∎ {Γ₀}{init})
              ~: deposit∈Γ⇒namesʳ {Γ = Γ₀} d∈
          in
            (txout′ x∈ ≡ ∃T₀ at oᵢ) × (T₀ ‼ᵒ oᵢ ≡ v -redeemableWith- K̂ A)
      )
      -- (v) dom sechash = ∅
    → dom sechash′ ≡ []
      -- (vi) dom κ = ∅
    → dom κ′ ≡ []
      --——————————————————————————————————————————————————————————————————————
    → ∃𝕣 ~′ Rᶜ
-}

  -- * Inductive case 1
  -- step₁ : ∀ {λˢ : 𝕃 Rˢ Γₜ} → let 𝕣 = 𝕃⇒ℝ λˢ in
  --     (-, 𝕣) ~′ Rᶜ
  --   → (Rˢ ⦊ λˢ) ~₁ (Rᶜ ⦊ λᶜ)
  --     --——————————————————————————————————————————————————————————————————————
  --   → (-, proj₂ λˢ) ~′ (λᶜ ∷ Rᶜ)

  -- step₁ : ∀ {𝕒 : 𝔸 Rˢ Γₜ} {𝕣′ : ℝ (Γₜ ∷ Rˢ ⊣ 𝕒)} →
  step₁ : ∀ {𝕒 : 𝔸 Rˢ Γₜ} {𝕣 : ℝ Rˢ} {𝕔 : ℾ (𝕒 .proj₂ .proj₂ .proj₁)} →
    -- let 𝕣 = drop-ℝ 𝕒 𝕣′ in
    let 𝕣′ = ℝ∷ {R = Rˢ} {Γₜ = Γₜ} 𝕒 𝕔 𝕣 in
      (-, 𝕣) ~′ Rᶜ
    → (Rˢ ⦊ 𝕒 , 𝕣′) ~₁ (Rᶜ ⦊ λᶜ)
      --——————————————————————————————————————————————————————————————————————
    → (-, 𝕣′) ~′ (λᶜ ∷ Rᶜ)

  -- * Inductive case 2
{-
  step₂ :
      ∃𝕣 ~′ Rᶜ
    → ∃𝕣 ~₂ λᶜ
      --——————————————————————————————————————————————————————————————————————
    → ∃𝕣 ~′ (λᶜ ∷ Rᶜ)
-}

_~_ _≁_ : S.Run → C.Run → Set
Rˢ ~ Rᶜ = ∃[ 𝕣 ] (Rˢ , 𝕣) ~′ Rᶜ
_≁_ = ¬_ ∘₂ _~_

private
  testPatternMatch-~₁ : ∀ {λˢ : 𝕃 Rˢ Γₜ}
    → (Rˢ ⦊ λˢ) ~₁ (Rᶜ ⦊ λᶜ)
    → ⊤
  testPatternMatch-~₁ coh
    with coh
  ... | [L] [1]  R≈ ∃Γ≈ vad hon d⊆ = tt

  testPatternMatch-~′ : ∀ (𝕣 : ℝ Rˢ)
    → (-, 𝕣) ~′ Rᶜ
    → ⊤
  testPatternMatch-~′ 𝕣 coh
    with coh
  ... | step₁ _ p
    with p
  ... | [L] [1]  R≈ ∃Γ≈ vad hon d⊆ = tt


  testPatternMatch-~ : Rˢ ~ Rᶜ → ⊤
  testPatternMatch-~ (𝕣 , coh) = {!!}
  --   with coh
  -- ... | step₁ _ ([L] [1] R≈ ∃Γ≈ vad hon d⊆) = tt

  {-
  ... | [L] [2]  R≈ ∃Γ≈ as≡ All∉ Hon⇒ ∃B h≡ h∈O unique-h h♯sechash = tt
  ... | [L] [3]  R≈ ∃Γ≈ committedA A∈per ∃B = tt
  ... | [L] [4]  R≈ ∃Γ≈ fresh-z = tt
  ... | [L] [5]  d≡ R≈ ∃Γ≈ = tt
  ... | [L] [6]  t≡ d≡ R≈ ∃Γ≈ fresh-y′ p⟦Δ⟧≡ As≡∅ = tt
  ... | [L] [7]  R≈ ∃Γ≈ fresh-ys ∃B ∃α a∈ ∃λ first-λᶜ = tt
  ... | [L] [8]  t≡ d≡ R≈ fresh-xs As≡∅ ∃Γ≈ = tt
  ... | [L] [9]  d≡ R≈ ∃Γ≈ frsg-x As≡∅ ∀≤t = tt
  ... | [L] [10] R≈ ∃Γ≈ ∃λ first-λᶜ = tt
  ... | [L] [11] R≈ ∃Γ≈ fresh-y = tt
  ... | [L] [12] R≈ ∃Γ≈ ∃λ first-λᶜ = tt
  ... | [L] [13] R≈ ∃Γ≈ fresh-ys = tt
  ... | [L] [14] R≈ ∃Γ≈ ∃λ first-λᶜ = tt
  ... | [L] [15] R≈ ∃Γ≈ fresh-y = tt
  ... | [R] [16] R≈ ∃Γ≈ fresh-y T ⊆ins T∈ first-λᶜ ¬coh = tt
  ... | [R] [17] R≈ ∃Γ≈ T ⊆ins ¬coh = tt
  ... | [L] [18] δ>0 ∃Γ≈ = tt
  -}
