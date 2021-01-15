{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Unit.NonEta
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Fin hiding (_<_; _≤_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Data.List.Properties using (∷-injective; length-map)
open import Data.List.Relation.Unary.Any renaming (map to Any-map)
open import Data.List.Relation.Unary.All renaming (lookup to All-lookup; map to All-map)
open import Data.List.Relation.Unary.All.Properties hiding (All-map)
open import Data.List.Relation.Unary.Any.Properties renaming (map⁺ to Any-map⁺)
open import Data.List.Relation.Binary.Pointwise using (decidable-≡)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Maybe renaming (map to Maybe-map)
open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary

open import AAOSL.Lemmas
open import AAOSL.Abstract.Hash
open import AAOSL.Abstract.DepRel

-- This module defines the DepRel type, which represents the class of AAOSLs we
-- consider, and proves properties about any DepRel.

module AAOSL.Abstract.Advancement
   -- A Hash function maps a bytestring into a hash.
   (hash    : ByteString → Hash)
   -- And is collision resistant
   (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)

   -- Indexes can be encoded in an injective way
   (encodeI     : ℕ → ByteString)
   (encodeI-inj : (m n : ℕ) → encodeI m ≡ encodeI n → m ≡ n)

   (dep  : DepRel)
 where

  -- Brings the DepRel names into scope instantiated
  -- for the module parameters in question.
  open DepRel dep

  hop-prog : ∀{m}(h : HopFrom m) → hop-tgt h ≢ m
  hop-prog = <⇒≢ ∘ hop-<

  hop-≤ : ∀{m}(h : HopFrom m) → hop-tgt h ≤ m
  hop-≤ = <⇒≤ ∘ hop-<

  depsof : ℕ → List ℕ
  depsof 0       = []
  depsof (suc i) = List-map hop-tgt (nats (lvlof (suc i)))

  depsof-ne : ∀ m → depsof m ≡ [] → m ≡ 0
  depsof-ne 0       hyp = refl
  depsof-ne (suc m) hyp =
    let le0 = trans (sym (length-map hop-tgt (nats (lvlof (suc m)))) )
                    (cong length hyp)
        le-nz = nats-length (lvlof-s m)
     in ⊥-elim (1≤0-⊥ (subst (1 ≤_) le0 le-nz))

  hopFromZ-⊥ : (h : HopFrom 0) → ⊥
  hopFromZ-⊥ h = fin0-⊥ (subst Fin lvlof-z h)
    where fin0-⊥ : Fin 0 → ⊥
          fin0-⊥ ()

  hop-tgt-is-dep : {m : ℕ}(h : HopFrom m)
                 → hop-tgt h ∈ depsof m
  hop-tgt-is-dep {0}     h = ⊥-elim (hopFromZ-⊥ h)
  hop-tgt-is-dep {suc m} h = Any-map⁺ (Any-map (cong hop-tgt) (nats-correct h))

  -- Two simple but useful lemmas made to work over our abstract
  -- index type.
  ≤-≢-mon : ∀{i j tgt} → tgt ≢ j → tgt ≤ j → i ≤ tgt → i ≢ j
  ≤-≢-mon tgt≢j tgt≤j i≤tgt i≡j
    = tgt≢j (sym (≤-antisym (subst (_≤ _) i≡j i≤tgt) tgt≤j))

  ≟ℕ-refl : (s : ℕ) → (s ≟ℕ s) ≡ yes refl
  ≟ℕ-refl s with s ≟ℕ s
  ...| no abs   = ⊥-elim (abs refl)
  ...| yes refl = refl

  ⊥-prop : (a b : ⊥) → a ≡ b
  ⊥-prop () ()

  ≟ℕ-neg : (m n : ℕ) → (p : m ≢ n) → (m ≟ℕ n) ≡ no p
  ≟ℕ-neg m n p with m ≟ℕ n
  ...| yes imp = ⊥-elim (p imp)
  ...| no  r   = cong no (fun-ext (λ x → ⊥-prop (r x) (p x)))

  HopFrom≢0 : ∀{j}(h : HopFrom j) → j ≢ 0
  HopFrom≢0 {j} h refl = hopFromZ-⊥ h

  open WithCryptoHash hash hash-cr

  -- This function is total, even though we won't always know a hash for every
  -- index.  That's ok, we only use the hashes of the relevant indexes.
  View : Set
  View = ℕ → Hash

  -- An inhabitant of 'Agree s t ixs' is a proof that the views s and t
  -- agree on the hash of every index i ∈ ixs.
  Agree : View → View → List ℕ → Set
  Agree v u = All (λ s → v s ≡ u s)

  -- Returns the list of hashes that the authenticator
  -- at the given index depends on.
  deps-hash : ℕ → View → List Hash
  deps-hash s tbl = List-map tbl (depsof s)

  -- TODO-2: Make auth, auth-inj-1 and auth-inj-2 module parameters
  -- TODO-1: Make sure the names are consistent with the paper

  --------------------------
  -- Defining authenticators

  -- Authenticators will depend on all p-auths of the
  -- dependencies of a node.
  auth : (s : ℕ) → Hash → View → Hash
  auth s h tbl = hash-concat (hash (encodeI s) ∷ h ∷ deps-hash s tbl)

  -- We will be using two separate injectivity functions. One is
  -- for the hash of the data in a node, which can't be the
  -- initial node!
  auth-inj-1 : {j : ℕ}{h₁ h₂ : Hash}{t₁ t₂ : View}
             → j ≢ 0
             → auth j h₁ t₁ ≡ auth j h₂ t₂
             → HashBroke ⊎ h₁ ≡ h₂
  auth-inj-1 {j} {h₁} {h₂} {t₁} {t₂} j≢s₀ hip
    with hash-concat-inj { hash (encodeI j) ∷ h₁ ∷ deps-hash j t₁ }
                         { hash (encodeI j) ∷ h₂ ∷ deps-hash j t₂ } hip
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ r  = inj₂ (proj₁ (∷-injective (proj₂ (∷-injective r))))

  -- The second one does induction on the list of dependencies.
  auth-inj-2 : {i : ℕ}{h : Hash}(t₁ t₂ : View)
             → auth i h t₁ ≡ auth i h t₂
             → HashBroke ⊎ Agree t₁ t₂ (depsof i)
  auth-inj-2 {i} {h} t₁ t₂ hip
    with hash-concat-inj { hash (encodeI i) ∷ h ∷ deps-hash i t₁ }
                         { hash (encodeI i) ∷ h ∷ deps-hash i t₂ } hip
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ r  = inj₂ (auth-inj-2-aux t₁ t₂ (depsof i) (proj₂ (∷-injective (proj₂ (∷-injective r)))))
    where
      auth-inj-2-aux : (t₁ t₂ : View)(l : List ℕ)
                     → List-map t₁ l ≡ List-map t₂ l
                     → Agree t₁ t₂ l
      auth-inj-2-aux t1 t2 [] hyp = []
      auth-inj-2-aux t1 t2 (x ∷ l) hyp = proj₁ (∷-injective hyp) ∷ auth-inj-2-aux t1 t2 l (proj₂ (∷-injective hyp))

  ------------------------
  ------------------------
  -- Advancement Proofs --
  ------------------------
  ------------------------

  -- Finally, advancement proofs in their simple variant
  data AdvPath : ℕ → ℕ → Set where
    AdvDone  : ∀{i} → AdvPath i i
    AdvThere : ∀{j i}
             → Hash -- datum digest
             → (h : HopFrom j)
             → AdvPath (hop-tgt h) i
             → AdvPath j i

  -- Override a view with a hash for a specific index.
  _∪₁_ : View → ℕ × Hash → View
  _∪₁_ tbl (s , h) s'
     with s ≟ℕ s'
  ...| yes _ = h
  ...| no  _ = tbl s'

  -- The rebuild function is, essentially, a transformer over
  -- the current view of the skiplog. It is PARAMOUNT to return
  -- a new 'view' of the world, as we can see in rebuild-⊕ lemma.
  -- Otherwise, it becomes seriously intricate to express
  -- that rebuilding the hash of index j "depends on" the rebuilt
  -- hashes of j's dependencies.
  rebuild : ∀{i j} → AdvPath j i → View → View
  rebuild {i} AdvDone tbl = tbl
  rebuild (AdvThere {j = j} x h prf) tbl
    = let tbl' = rebuild prf tbl
       in tbl' ∪₁ (j , auth j x tbl')

  lemma1 : ∀{j i} → AdvPath j i → i ≤ j
  lemma1 AdvDone              = ≤-refl
  lemma1 {j} (AdvThere x h a) = ≤-trans (lemma1 a) (hop-≤ h)

  rebuild-tgt-lemma : ∀{j i}(a : AdvPath j i){t : View}
                    → rebuild a t i ≡ t i
  rebuild-tgt-lemma AdvDone = refl
  rebuild-tgt-lemma {j} {i} (AdvThere x h a)
    rewrite ≟ℕ-neg j i (<⇒≢ (≤-<-trans (lemma1 a) (hop-< h)) ∘ sym)
          = rebuild-tgt-lemma a

  lemma2 : ∀{i}(a : AdvPath i i) → a ≡ AdvDone
  lemma2 AdvDone = refl
  lemma2 (AdvThere x h a)
    = ⊥-elim (hop-prog h (sym (≤-antisym (lemma1 a) (hop-≤ h))))

  -- Lemma3 states that if a hop exists, then it is not from
  -- s₀. This is necessary to eliminate some nasty cases.
  lemma3 : ∀{j i} → (h : HopFrom j) → AdvPath (hop-tgt h) i → j ≢ 0
  lemma3 h a = HopFrom≢0 h

  ----------------------
  -- Proof Splitting  --
  ----------------------

  _⊕_ : ∀{j k i} → AdvPath j k → AdvPath k i → AdvPath j i
  AdvDone          ⊕ rest = rest
  (AdvThere d h a) ⊕ rest = AdvThere d h (a ⊕ rest)

  ⊕-id-r : ∀{j i}(a : AdvPath j i) → a ⊕ AdvDone ≡ a
  ⊕-id-r AdvDone = refl
  ⊕-id-r (AdvThere x h a) = cong (AdvThere x h) (⊕-id-r a)

  -- A value of type 'i ∈AP a' illustrates index i as a dependency
  -- of 'a'.
  data _∈AP_ (i₀ : ℕ) : {j i : ℕ} → AdvPath j i → Set where
    hereTgtDone  : i₀ ∈AP (AdvDone {i₀})

    hereTgtThere : ∀{i}{d : Hash}{hop : HopFrom i₀}{a : AdvPath (hop-tgt hop) i}
                 → i₀ ∈AP (AdvThere d hop a)

    step         : ∀{i j}{d : Hash}{hop : HopFrom j}{a : AdvPath (hop-tgt hop) i}
                 → i₀ ≢ j
                 → i₀ ∈AP a
                 → i₀ ∈AP (AdvThere d hop a)

  ∈AP-src : ∀{j i}{a : AdvPath j i}
          → j ∈AP a
  ∈AP-src {a = AdvDone}        = hereTgtDone
  ∈AP-src {a = AdvThere x h a} = hereTgtThere

  ∈AP-tgt : ∀{j i}{a : AdvPath j i}
          → i ∈AP a
  ∈AP-tgt {a = AdvDone}        = hereTgtDone
  ∈AP-tgt {a = AdvThere x h a} = step (<⇒≢ (≤-<-trans (lemma1 a) (hop-< h))) ∈AP-tgt

  ∈AP-≤ : ∀{j i}{a : AdvPath j i}
               → {i0 : ℕ} → i0 ∈AP a
               → i0 ≤ j
  ∈AP-≤ hereTgtDone  = ≤-refl
  ∈AP-≤ hereTgtThere = ≤-refl
  ∈AP-≤ (step _ hyp) = ≤-trans (∈AP-≤ hyp) (hop-≤ _)

  ∈AP-≥ : ∀{j i}{a : AdvPath j i}
        → {i0 : ℕ} → i0 ∈AP a
        → i ≤ i0
  ∈AP-≥ hereTgtDone = ≤-refl
  ∈AP-≥ {a = a} hereTgtThere = lemma1 a
  ∈AP-≥ (step _ hyp) = ∈AP-≥ hyp


  rebuild-⊕ : ∀{j k i}
             → {t : View}
             → (a₁ : AdvPath j k)
             → (a₂ : AdvPath k i)
             → ∀{l} → l ∈AP a₂
             → rebuild (a₁ ⊕ a₂) t l ≡ rebuild a₂ t l
  rebuild-⊕ AdvDone a₂ hyp = refl
  rebuild-⊕ {j} (AdvThere x h a₁) a₂ {l} hyp
    with j ≟ℕ l
  ...| yes nope = ⊥-elim (≤-≢-mon (hop-prog h) (hop-≤ h)
                          (≤-trans (∈AP-≤ hyp) (lemma1 a₁)) (sym nope))
  ...| no ok    = rebuild-⊕ a₁ a₂ hyp

  ∈AP-cut : ∀{j k i}
          → (a : AdvPath j i)
          → k ∈AP a
          → Σ (AdvPath j k × AdvPath k i)
              (λ { (x , y) → a ≡ x ⊕ y })
  ∈AP-cut AdvDone hereTgtDone
    = (AdvDone , AdvDone) , refl
  ∈AP-cut (AdvThere d h a) hereTgtThere
    = (AdvDone , AdvThere d h a) , refl
  ∈AP-cut (AdvThere d h a) (step x prf)
    with ∈AP-cut a prf
  ...| xy , ind = (AdvThere d h (proj₁ xy) , proj₂ xy)
                , cong (AdvThere d h) ind

  ∈AP-cut₁ : ∀{j k i}
           → (a : AdvPath j i)
           → k ∈AP a
           → AdvPath k i
  ∈AP-cut₁ a prf = proj₂ (proj₁ (∈AP-cut a prf))

  ∈AP-∈-cut
    : ∀{j k i}
    → (a : AdvPath j i)
    → (prf : k ∈AP a)
    → ∀{m} → m ∈AP a → m ≤ k
    → m ∈AP (∈AP-cut₁ a prf)
  ∈AP-∈-cut AdvDone hereTgtDone m∈ap hyp = m∈ap
  ∈AP-∈-cut (AdvThere _ _ _) hereTgtThere m∈ap hyp = m∈ap
  ∈AP-∈-cut (AdvThere d h a) (step x prf) hereTgtThere hyp
    = ⊥-elim (<⇒≱ (hop-< h) (≤-trans hyp (∈AP-≤ prf)))
  ∈AP-∈-cut (AdvThere d h a) (step x prf) (step x₁ m∈ap) hyp
    = ∈AP-∈-cut a prf m∈ap hyp

  ∈AP-cut₁-rebuild
    : ∀{j k i}
    → (a : AdvPath j i)
    → (prf : k ∈AP a)
    → {s : ℕ} → (s ∈AP (∈AP-cut₁ a prf))
    → ∀{t} → rebuild a t s ≡ rebuild (∈AP-cut₁ a prf) t s
  ∈AP-cut₁-rebuild a prf s∈cut {t}
    with ∈AP-cut a prf
  ...| (x , y) , refl = rebuild-⊕ x y s∈cut

  ∈AP-⊕ : ∀{j i₁ k i₂ i}
        → {e  : AdvPath j k}{a₁ : AdvPath k i₁}
        → {a₂ : AdvPath k i₂}
        → i ∈AP (e ⊕ a₁)
        → i ∈AP a₂
        → i ∈AP a₁
  ∈AP-⊕ {e = AdvDone}        hyp1 hyp2 = hyp1
  ∈AP-⊕ {e = AdvThere x h e} hereTgtThere   hyp2
    with ≤-antisym (∈AP-≤ hyp2) (lemma1 (AdvThere x h e))
  ...| refl = ⊥-elim (hop-prog h (≤-antisym (hop-≤ h) (lemma1 e)))
  ∈AP-⊕ {e = AdvThere x h e} (step x₁ hyp1) hyp2 = ∈AP-⊕ hyp1 hyp2

  ∈AP-point' : ∀{j k i}
             → {a₁ : AdvPath j k}
             → {a₂ : AdvPath k i}
             → {m : ℕ} → m ∈AP a₁ → m ∈AP a₂
             → m ≡ k
  ∈AP-point' hereTgtDone h2 = refl
  ∈AP-point' {a₁ = AdvThere d h a₁} {a₂} hereTgtThere h2
    = ⊥-elim (≤-≢-mon (≤-≢-mon (hop-prog h) (hop-≤ h) (lemma1 a₁) ∘ sym)
                      (∈AP-≤ h2)
                      (lemma1 (AdvThere d h a₁)) refl)
  ∈AP-point' (step x h1) h2 = ∈AP-point' h1 h2

  ∈AP-point'' : ∀{j₁ j₂ i₁ i₂}
              → {a₁ : AdvPath j₁ i₁}
              → {a₂ : AdvPath j₂ i₂}
              → j₂ < i₁
              → {i : ℕ} → i ∈AP a₁ → i ∈AP a₂
              → ⊥
  ∈AP-point'' j<i hereTgtDone h2
    = (<⇒≢ j<i) (≤-antisym (<⇒≤ j<i) (∈AP-≤ h2))
  ∈AP-point'' {a₁ = a₁} j<i hereTgtThere h2
    = (<⇒≢ j<i) (≤-antisym (<⇒≤ j<i) (≤-trans (lemma1 a₁) (∈AP-≤ h2)))
  ∈AP-point'' j<i (step x h1) h2 = ∈AP-point'' j<i h1 h2

  ∈AP-point : ∀{j₁ j₂ i₁ i₂}
            → {a₁ : AdvPath j₁ i₁}
            → {a₂ : AdvPath j₂ i₂}
            → j₂ ≤ i₁
            → {i : ℕ} → i ∈AP a₁ → i ∈AP a₂
            → j₂ ≡ i₁ × i ≡ j₂
  ∈AP-point {j₂ = j₂} {i₁ = i₁} j₂≤i₁ h1 h2
    with j₂ ≟ℕ i₁
  ...| no abs = ⊥-elim (∈AP-point'' (≤∧≢⇒< j₂≤i₁ abs) h1 h2)
  ...| yes refl = refl , ∈AP-point' h1 h2

  ∈AP-AdvDone-≡ : ∀{i j}
                → i ∈AP (AdvDone {j})
                → i ≡ j
  ∈AP-AdvDone-≡ hereTgtDone = refl

  -- It is important that we can split proofs. Here, we know that 'a'
  -- and the guide are proofs that come from jump from the same source, j.
  split-⊕ : ∀{J j i}
           → {H : HopFrom J}
           → {h : HopFrom j}
           → j ≤ J
           → hop-tgt H < hop-tgt h
           → i ≤ hop-tgt H
           → (a : AdvPath (hop-tgt h) i)
           → Σ (AdvPath (hop-tgt h) (hop-tgt H) × AdvPath (hop-tgt H) i)
               (λ { (x , y) → a ≡ x ⊕ y })
  split-⊕ j≤J H<h i≤H AdvDone
    = ⊥-elim (≤-≢-mon (<⇒≢ H<h) (<⇒≤ H<h) i≤H refl)
  split-⊕ {i = i} {H} {h} j≤J H<h i≤H (AdvThere d h' a)
    with hop-tgt h' ≟ℕ hop-tgt H
  ...| yes sameHop = (AdvThere d h' (subst (AdvPath (hop-tgt h')) sameHop AdvDone)
                     , subst (λ P → AdvPath P i) sameHop a)
                     , aux sameHop a
     where
      aux : ∀{i j k}{h : HopFrom j} → (stop : hop-tgt h ≡ k)
          → (a : AdvPath (hop-tgt h) i)
          → AdvThere d h a
            ≡ (AdvThere d h (subst (AdvPath (hop-tgt h)) stop AdvDone)
               ⊕ subst (λ P → AdvPath P i) stop a)
      aux refl a = refl
  ...| no  diffHop
    with ≤-total (hop-tgt h') (hop-tgt H)
  ...| inj₁ crossover with hops-nested-or-nonoverlapping (≤∧≢⇒< crossover diffHop)
                                                         H<h
  ...| abs = ⊥-elim (≤-≢-mon (mmm (hop-≤ h) (hop-prog h) j≤J) (≤-trans (hop-≤ h) j≤J) abs refl)
     where mmm : ∀{h j J} → h ≤ j → h ≢ j → j ≤ J → h ≢ J
           mmm h≤j h≢j j≤J refl = h≢j (≤-antisym h≤j j≤J)
  split-⊕ {i = i} {H} {h} j≤J H<h i≤H (AdvThere d h' a)
     | no diffHop
     | inj₂ go
    with split-⊕ {H = H} (≤-trans (hop-≤ h) j≤J) (≤∧≢⇒< go (diffHop ∘ sym)) i≤H a
  ...| ((x , y) , prf) = (AdvThere d h' x , y) , cong (AdvThere d h') prf

  ---------------------
  -- Evolutionary CR --
  ---------------------

  -- The type 'AgreeOnCommon t₁ t₂ a₁ a₂', or 'AOC' for short, is inhabited if
  -- and only if the advancement proofs a₁ and a₂ agree on the hash they rebuild
  -- for every index that is visited by both. Moreover, the views must also
  -- agree on the dependencies of said indexes.
  data AOC (t₁ t₂ : View)
      : ∀{i₁ i₂ j} → AdvPath j i₁ → AdvPath j i₂ → Set where
    PDoneDone : ∀{i} → t₁ i ≡ t₂ i → AOC t₁ t₂ {i} {i} AdvDone AdvDone

    --                        h
    --             ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
    --             |                     |
    --             |         ⌜⁻⁻⁻ a₁ ⁻⁻⁻⁻|
    --             |         |           |
    --   i₂  ⋯  hop-tgt h  ≤ i₁          j
    PDoneL : ∀{j i₁ i₂}{d}{h : HopFrom j}
           → (a₁ : AdvPath j i₁)
           → (a₂ : AdvPath (hop-tgt h) i₂)
           → hop-tgt h ≤ i₁
           → rebuild a₁ t₁ j ≡ rebuild (AdvThere d h a₂) t₂ j
           → AOC t₁ t₂ a₁ (AdvThere d h a₂)

    PDoneR : ∀{j i₁ i₂}{d}{h : HopFrom j}
           → (a₁ : AdvPath (hop-tgt h) i₁)
           → (a₂ : AdvPath j i₂)
           → hop-tgt h ≤ i₂
           → rebuild (AdvThere d h a₁) t₁ j ≡ rebuild a₂ t₂ j
           → AOC t₁ t₂ (AdvThere d h a₁) a₂

    PCong : ∀{j i₁ i₂}{d}{h : HopFrom j}
          → i₁ ≤ i₂
          → (a₁ : AdvPath (hop-tgt h) i₁)
          → (a₂ : AdvPath (hop-tgt h) i₂)
          → Agree (rebuild a₁ t₁) (rebuild a₂ t₂) (depsof j)
          → AOC t₁ t₂ a₁ a₂
          → AOC t₁ t₂ (AdvThere d h a₁)
                      (AdvThere d h a₂)

    PMeetR : ∀{j i₁ i₂ d}{h₁ h₂ : HopFrom j}
           → (e  : AdvPath (hop-tgt h₁) (hop-tgt h₂))
           → (a₁ : AdvPath (hop-tgt h₂) i₁)
           → (a₂ : AdvPath (hop-tgt h₂) i₂)
           → hop-tgt h₂ < hop-tgt h₁
           → Agree (rebuild (e ⊕ a₁) t₁) (rebuild a₂ t₂) (depsof j)
           → AOC t₁ t₂ a₁ a₂
           → AOC t₁ t₂ (AdvThere d h₁ (e ⊕ a₁))
                       (AdvThere d h₂ a₂)

    PMeetL : ∀{j i₁ i₂ d}{h₁ h₂ : HopFrom j}
           → (e  : AdvPath (hop-tgt h₂) (hop-tgt h₁))
           → (a₁ : AdvPath (hop-tgt h₁) i₁)
           → (a₂ : AdvPath (hop-tgt h₁) i₂)
           → hop-tgt h₁ < hop-tgt h₂
           → Agree (rebuild a₁ t₁) (rebuild (e ⊕ a₂) t₂) (depsof j)
           → AOC t₁ t₂ a₁ a₂
           → AOC t₁ t₂ (AdvThere d h₁ a₁)
                       (AdvThere d h₂ (e ⊕ a₂))

  -- We use the 'TERMINATING' pragma because we use a recursive call on
  -- an argument that Agda can't infer being structurally smaller.
  -- TODO-1: provide clear and detailed explanation of this, which argument, why smaller?
  -- An interesting longer-term TODO-2 would be to use 'Sized Types' to inform
  -- the typechecker of this fact, or perhaps a custom-made moral equivalent.
  {-# TERMINATING #-}
  aoc : ∀{i₁ i₂ j}
      → i₁ ≤ i₂ -- wlog
      → (t₁ t₂ : View)(a₁ : AdvPath j i₁)(a₂ : AdvPath j i₂)
      → rebuild a₁ t₁ j ≡ rebuild a₂ t₂ j
      → HashBroke ⊎ AOC t₁ t₂ a₁ a₂
  aoc _ t1 t2 AdvDone AdvDone hip
    = inj₂ (PDoneDone hip)
  aoc _ t1 t2 AdvDone (AdvThere x h a2) hip
    = inj₂ (PDoneL AdvDone a2 (hop-≤ h) hip)
  aoc _ t1 t2 (AdvThere x h a1) AdvDone hip
    = inj₂ (PDoneR a1 AdvDone (hop-≤ h) hip)
  aoc {i₁} {i₂} {j} k t₁ t₂ (AdvThere d₁ h₁ a₁) (AdvThere d₂ h₂ a₂) hip
    with ≤-total i₂ (hop-tgt h₁)
  ...| inj₂ h₁≤i₂ = inj₂ (PDoneR a₁ (AdvThere d₂ h₂ a₂) h₁≤i₂ hip)
  ...| inj₁ go
    rewrite ≟ℕ-refl j
    with auth-inj-1 {j} {d₁} {d₂} (lemma3 h₁ a₁) hip
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ refl
    with auth-inj-2 {j} {d₁} (rebuild a₁ t₁) (rebuild a₂ t₂) hip
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ agree
    with h₁ ≟Hop h₂
  ...| yes refl
    with witness (hop-tgt-is-dep h₁) agree
  ...| wit rewrite (≟ℕ-refl (hop-tgt h₁))
    with aoc k t₁ t₂ a₁ a₂ wit
  ...| inj₁ hb  = inj₁ hb
  ...| inj₂ rec = inj₂ (PCong k a₁ a₂ agree rec)
  aoc {i₁} {i₂} {j} k t₁ t₂ (AdvThere d₁ h₁ a₁) (AdvThere d₂ h₂ a₂) hip
     | inj₁ go
     | inj₂ refl
     | inj₂ agree
     | no diffHop
    with ≤-total (hop-tgt h₁) (hop-tgt h₂)
  ...| inj₁ h₁<h₂ with split-⊕ ≤-refl (≤∧≢⇒< h₁<h₂ (diffHop ∘ hop-tgt-inj)) go a₂
  ...| ((x , y) , refl)
    with aoc k t₁ t₂ a₁ y (trans (witness (hop-tgt-is-dep h₁) agree) (rebuild-⊕ x y ∈AP-src))
  ...| inj₁ hb  = inj₁ hb
  ...| inj₂ res = inj₂ (PMeetL x a₁ y (≤∧≢⇒< h₁<h₂ (diffHop ∘ hop-tgt-inj)) agree res)
  aoc {j = j} k t₁ t₂ (AdvThere d₁ h₁ a₁) (AdvThere d₂ h₂ a₂) hip
     | inj₁ go
     | inj₂ refl
     | inj₂ agree
     | no diffHop
     | inj₂ h₂<h₁ with split-⊕ ≤-refl (≤∧≢⇒< h₂<h₁ (diffHop ∘ hop-tgt-inj ∘ sym))
                         (≤-trans k (lemma1 a₂)) a₁
  ...| ((x , y) , refl)
    with aoc k t₁ t₂ y a₂ (trans (sym (rebuild-⊕ x y ∈AP-src))
                                 (witness (hop-tgt-is-dep h₂) agree))
  ...| inj₁ hb  = inj₁ hb
  ...| inj₂ res = inj₂ (PMeetR x y a₂ (≤∧≢⇒< h₂<h₁ (diffHop ∘ hop-tgt-inj ∘ sym)) agree res)

  -- TODO: rename AGREEONCOMMON for consistency with paper, or comment to make connection
  aoc-correct : ∀{j i₁ i₂}{a₁ : AdvPath j i₁}{a₂ : AdvPath j i₂}
              → {t₁ t₂ : View}
              → AOC t₁ t₂ a₁ a₂
              → {i : ℕ} → i ∈AP a₁ → i ∈AP a₂
              → HashBroke ⊎ rebuild a₁ t₁ i ≡ rebuild a₂ t₂ i
  aoc-correct (PDoneDone x) hereTgtDone hereTgtDone = inj₂ x
  aoc-correct (PDoneL a₁ a₂ x x₁) hyp1 hereTgtThere = inj₂ x₁
  aoc-correct {j} {t₁ = t₁} {t₂} (PDoneL {d = d} {h} a₁ a₂ x x₁) {i} hyp1 (step x₂ hyp2)
    with j ≟ℕ i
  ...| yes nope = ⊥-elim (x₂ (sym nope))
  ...| no  ok
    with a₁
  ...| AdvDone rewrite ∈AP-AdvDone-≡ hyp1 = ⊥-elim (x₂ refl)
  ...| AdvThere d₁ h₁ a₁'
    with ∈AP-point x hyp1 hyp2
  ...| refl , refl
    with j ≟ℕ hop-tgt h
  ...| yes nope = ⊥-elim (x₂ (sym nope))
  ...| no ok' rewrite ≟ℕ-refl j
    with auth-inj-1 {h₁ = d₁} {d} (HopFrom≢0 h) x₁
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ refl
    with auth-inj-2 {j} {d₁} (rebuild a₁' t₁) (rebuild a₂ t₂) x₁
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ r  = inj₂ (witness (hop-tgt-is-dep h) r)
  aoc-correct (PDoneR a₁ a₂ x x₁) hereTgtThere hyp2 = inj₂ x₁
  aoc-correct {j} {t₁ = t₁} {t₂} (PDoneR {d = d} {h} a₁ a₂ x x₁) {i} (step x₂ hyp1) hyp2
    with j ≟ℕ i
  ...| yes nope = ⊥-elim (x₂ (sym nope))
  ...| no  ok
    with a₂
  ...| AdvDone rewrite ∈AP-AdvDone-≡ hyp2 = ⊥-elim (x₂ refl)
  ...| AdvThere d₂ h₂ a₂'
    with ∈AP-point x hyp2 hyp1
  ...| refl , refl
    with j ≟ℕ hop-tgt h
  ...| yes nope = ⊥-elim (x₂ (sym nope))
  ...| no ok' rewrite ≟ℕ-refl j
    with auth-inj-1 {h₁ = d₂} {d} (HopFrom≢0 h) (sym x₁)
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ refl
    with auth-inj-2 {j} {d₂} (rebuild a₁ t₁) (rebuild a₂' t₂) x₁
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ r  = inj₂ (witness (hop-tgt-is-dep h) r)
  aoc-correct {j} {t₁ = t₁} {t₂} (PCong x a₁ a₂ x₁ aoc₁) hereTgtThere hereTgtThere
    rewrite ≟ℕ-refl j
          | List-map-≡-All (rebuild a₁ t₁) (rebuild a₂ t₂) (depsof j) x₁
          = inj₂ refl
  aoc-correct (PCong x a₁ a₂ x₁ aoc₁) hereTgtThere (step x₂ hyp2)
    = ⊥-elim (x₂ refl)
  aoc-correct (PCong x a₁ a₂ x₁ aoc₁) (step x₂ hyp1) hereTgtThere
    = ⊥-elim (x₂ refl)
  aoc-correct {j} (PCong x a₁ a₂ x₁ aoc₁) {i} (step x₂ hyp1) (step x₃ hyp2)
    with j ≟ℕ i
  ...| yes nope = ⊥-elim (x₂ (sym nope))
  ...| no  ok   = aoc-correct aoc₁ hyp1 hyp2
  aoc-correct {j} {t₁ = t₁} {t₂} (PMeetR e a₁ a₂ x₁ x₂ aoc₁) hereTgtThere hereTgtThere
    rewrite ≟ℕ-refl j
          | List-map-≡-All (rebuild (e ⊕ a₁) t₁) (rebuild a₂ t₂) (depsof j) x₂
          = inj₂ refl
  aoc-correct (PMeetR e a₁ a₂ x₁ x₂ aoc₁) hereTgtThere (step x₃ hyp2)
    = ⊥-elim (x₃ refl)
  aoc-correct (PMeetR e a₁ a₂ x₁ x₂ aoc₁) (step x₃ hyp1) hereTgtThere
    = ⊥-elim (x₃ refl)
  aoc-correct {j} (PMeetR e a₁ a₂ x₁ x₂ aoc₁) {i} (step x₃ hyp1) (step x₄ hyp2)
    with j ≟ℕ i
  ...| yes nope = ⊥-elim (x₃ (sym nope))
  ...| no  ok
    with aoc-correct aoc₁ (∈AP-⊕ hyp1 hyp2) hyp2
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ r  = inj₂ (trans (rebuild-⊕ e a₁ (∈AP-⊕ hyp1 hyp2)) r)

  aoc-correct {j} {t₁ = t₁} {t₂} (PMeetL e a₁ a₂ x₁ x₂ aoc₁) hereTgtThere hereTgtThere
    rewrite ≟ℕ-refl j
          | List-map-≡-All (rebuild a₁ t₁) (rebuild (e ⊕ a₂) t₂) (depsof j) x₂
          = inj₂ refl
  aoc-correct (PMeetL e a₁ a₂ x₁ x₂ aoc₁) hereTgtThere (step x₃ hyp2)
    = ⊥-elim (x₃ refl)
  aoc-correct (PMeetL e a₁ a₂ x₁ x₂ aoc₁) (step x₃ hyp1) hereTgtThere
    = ⊥-elim (x₃ refl)
  aoc-correct {j} (PMeetL e a₁ a₂ x₁ x₂ aoc₁) {i} (step x₃ hyp1) (step x₄ hyp2)
    with j ≟ℕ i
  ...| yes nope = ⊥-elim (x₃ (sym nope))
  ...| no  ok
    with aoc-correct aoc₁ hyp1 (∈AP-⊕ hyp2 hyp1)
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ r  = inj₂ (trans r (sym (rebuild-⊕ e a₂ (∈AP-⊕ hyp2 hyp1))))

  AgreeOnCommon : ∀{j i₁ i₂}
                → {t₁ t₂ : View}
                → (a₁ : AdvPath j i₁)(a₂ : AdvPath j i₂)
                → rebuild a₁ t₁ j ≡ rebuild a₂ t₂ j
                → {i : ℕ} → i ∈AP a₁ → i ∈AP a₂
                → HashBroke ⊎ rebuild a₁ t₁ i ≡ rebuild a₂ t₂ i
  AgreeOnCommon {i₁ = i₁} {i₂} {t₁} {t₂} a₁ a₂ rebuild-to-j i∈a₁ i∈a₂
     with ≤-total i₁ i₂
  ...| inj₁ i₁≤i₂ with aoc i₁≤i₂ t₁ t₂ a₁ a₂ rebuild-to-j
  ...|              inj₁ hb = inj₁ hb
  ...|              inj₂ xx = aoc-correct xx i∈a₁ i∈a₂

  AgreeOnCommon {i₁ = i₁} {i₂} {t₁} {t₂} a₁ a₂ rebuild-to-j i∈a₁ i∈a₂
     | inj₂ i₂≤i₁ with aoc i₂≤i₁ t₂ t₁ a₂ a₁ (sym rebuild-to-j)
  ...|              inj₁ hb = inj₁ hb
  ...|              inj₂ xx with aoc-correct xx i∈a₂ i∈a₁
  ...|                        inj₁ hb = inj₁ hb
  ...|                        inj₂ xx1 = inj₂ (sym xx1)

  AgreeOnCommon-∈ : ∀{j₁ j₂ i₁ i₂}
                → {t₁ t₂ : View}
                → (a₁ : AdvPath j₁ i₁)(a₂ : AdvPath j₂ i₂)
                → j₂ ∈AP a₁
                → rebuild a₁ t₁ j₂ ≡ rebuild a₂ t₂ j₂
                → {i : ℕ} → i ∈AP a₁ → i ∈AP a₂
                → HashBroke ⊎ rebuild a₁ t₁ i ≡ rebuild a₂ t₂ i
  AgreeOnCommon-∈ a₁ a₂ j2∈a1 hyp ia1 ia2
    with ∈AP-cut a₁ j2∈a1
  ...| ((a₁₁ , a₁₂) , refl)
    with AgreeOnCommon a₁₂ a₂ (trans (sym (rebuild-⊕ a₁₁ a₁₂ ∈AP-src)) hyp) (∈AP-⊕ ia1 ia2) ia2
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ res = inj₂ (trans (rebuild-⊕ a₁₁ a₁₂ (∈AP-⊕ ia1 ia2)) res)


  -----------------------
  -- Membership Proofs --
  -----------------------

  -- A membership proof for i is simply an advancement proof from j to i,
  -- a digest of the data in i and the authenticators that i depends on (which
  -- come in the view)
  MembershipProof : ℕ → ℕ → Set
  MembershipProof j i = AdvPath j i × Hash × i ≢ 0

  mbr-datum : ∀{j i} → MembershipProof j i → Hash
  mbr-datum (_ , d , _) = d

  mbr-proof : ∀{j i} → MembershipProof j i → AdvPath j i
  mbr-proof (p , _ , _) = p

  mbr-not-init : ∀{j i} → MembershipProof j i → i ≢ 0
  mbr-not-init (_ , _ , m) = m

  -- Rebuilding it is the same as rebuilding an advancement proof, but we
  -- explicitely compute the authenticator at i.
  rebuildMP : ∀{j i} → MembershipProof j i → View → View
  rebuildMP {j} {i} mbr t = rebuild (mbr-proof mbr)
                                    (t ∪₁ (i , auth i (mbr-datum mbr) t))

  semi-evo-cr : ∀{j i₁ i₂}{t₁ t₂ : View}
         → (a₁ : AdvPath j i₁)
         → (a₂ : AdvPath j i₂)
         → rebuild a₁ t₁ j ≡ rebuild a₂ t₂ j
         → ∀{s₁ s₂ tgt}{u₁ u₂ : View}
         → (m₁ : MembershipProof s₁ tgt)(m₂ : MembershipProof s₂ tgt)
         → s₁ ∈AP a₁ → s₂ ∈AP a₂
         → tgt ∈AP a₁ → tgt ∈AP a₂
         → tgt ≢ 0
         → rebuildMP m₁ u₁ s₁ ≡ rebuild a₁ t₁ s₁
         → rebuildMP m₂ u₂ s₂ ≡ rebuild a₂ t₂ s₂
         → HashBroke ⊎ (mbr-datum m₁ ≡ mbr-datum m₂)
  semi-evo-cr {t₁ = t₁} {t₂} a₁ a₂ hyp {tgt = tgt} {u₁} {u₂} m₁ m₂ s₁∈a₁ s₂∈a₂ t∈a₁ t∈a₂ t≢0 c₁ c₂
     with AgreeOnCommon (mbr-proof m₁) (∈AP-cut₁ a₁ s₁∈a₁)
                       (trans c₁ (∈AP-cut₁-rebuild a₁ s₁∈a₁ ∈AP-src {t₁}))
                       ∈AP-tgt (∈AP-∈-cut a₁ s₁∈a₁ t∈a₁ (lemma1 (mbr-proof m₁)))
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ hyp1
    with AgreeOnCommon (mbr-proof m₂) (∈AP-cut₁ a₂ s₂∈a₂)
                       (trans c₂ (∈AP-cut₁-rebuild a₂ s₂∈a₂ ∈AP-src {t₂}))
                       ∈AP-tgt (∈AP-∈-cut a₂ s₂∈a₂ t∈a₂ (lemma1 (mbr-proof m₂)))
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ hyp2
    with AgreeOnCommon a₁ a₂ hyp t∈a₁ t∈a₂
  ...| inj₁ hb   = inj₁ hb
  ...| inj₂ hyp3
    rewrite sym (∈AP-cut₁-rebuild a₁ s₁∈a₁
                  (∈AP-∈-cut a₁ s₁∈a₁ t∈a₁ (lemma1 (mbr-proof m₁))) {t₁})
          | sym (∈AP-cut₁-rebuild a₂ s₂∈a₂
                  (∈AP-∈-cut a₂ s₂∈a₂ t∈a₂ (lemma1 (mbr-proof m₂))) {t₂})

    with trans hyp1 (trans hyp3 (sym hyp2))
  ...| half     with rebuild-tgt-lemma (mbr-proof m₁)
                       {u₁ ∪₁ (tgt , auth tgt (mbr-datum m₁) u₁) }
                   | rebuild-tgt-lemma (mbr-proof m₂)
                       {u₂ ∪₁ (tgt , auth tgt (mbr-datum m₂) u₂) }
  ...| l1 | l2
    rewrite ≟ℕ-refl tgt = auth-inj-1 {tgt} {mbr-datum m₁} {mbr-datum m₂} t≢0 (trans (sym l1) (trans half l2))
