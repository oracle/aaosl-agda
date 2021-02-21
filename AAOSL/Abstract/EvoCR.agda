{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2021 Victor C Miraldo and Oracle and/or its affiliates.
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
open import Relation.Binary.Definitions
open import Relation.Nullary

open import AAOSL.Lemmas
open import AAOSL.Abstract.Hash
open import AAOSL.Abstract.DepRel

module AAOSL.Abstract.EvoCR
   -- A Hash function maps a bytestring into a hash.
   (hash    : ByteString → Hash)
   -- And is collision resistant
   (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)

   -- Indexes can be encoded in an injective way
   (encodeI     : ℕ → ByteString)
   (encodeI-inj : (m n : ℕ) → encodeI m ≡ encodeI n → m ≡ n)

   (dep  : DepRel)
 where

  open WithCryptoHash hash hash-cr
  open import AAOSL.Abstract.Advancement hash hash-cr encodeI encodeI-inj dep
  open DepRel dep

  -- Returns the last element on path a that is smaller than k
  last-bef : ∀{j i k}(a : AdvPath j i)(i<k : i < k)(k≤j : k ≤′ j) → ℕ
  last-bef {j} a i<k ≤′-refl = j
  -- TODO-1 : The same or similar proof is repeated numerous times below; refactor for clarity
  last-bef AdvDone i<k (≤′-step k≤j) = ⊥-elim (1+n≰n (≤-unstep (≤-trans i<k (≤′⇒≤ k≤j))))
  last-bef {k = k} (AdvThere d h a) i<k (≤′-step k≤j)
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = hop-tgt h
  ...| no th>k = last-bef a i<k (≤⇒≤′ (≰⇒≥ th>k))

  last-bef-correct : ∀{j i k}(a : AdvPath j i)(i<k : i < k)(k≤j : k ≤′ j)
                   → last-bef a i<k k≤j ∈AP a
  last-bef-correct {j} a i<k ≤′-refl = ∈AP-src
  last-bef-correct AdvDone i<k (≤′-step k≤j) = ⊥-elim (1+n≰n (≤-unstep (≤-trans i<k (≤′⇒≤ k≤j))))
  last-bef-correct {k = k} (AdvThere d h a) i<k (≤′-step k≤j)
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = step (<⇒≢ (hop-< h)) ∈AP-src
  ...| no th>k
    with last-bef-correct a i<k (≤⇒≤′ (≰⇒≥ th>k))
  ...| ind = step (<⇒≢ (≤-trans (s≤s (∈AP-≤ ind)) (hop-< h))) ind

  lemma5-hop : ∀{j i}(a : AdvPath j i)
             → ∀{k} → j < k
             → (h : HopFrom k) → hop-tgt h ≤ j → i ≤ hop-tgt h → hop-tgt h ∈AP a
  lemma5-hop {j} a j<k h th≤j i≤th
    with hop-tgt h ≟ℕ j
  ...| yes th≡j rewrite th≡j = ∈AP-src
  ...| no th≢j
    with a
  ...| AdvDone rewrite ≤-antisym th≤j i≤th = hereTgtDone
  ...| (AdvThere x h' a')
    with hop-tgt h' ≟ℕ hop-tgt h
  ...| yes th'≡th rewrite sym th'≡th = step (<⇒≢ (hop-< h')) ∈AP-src
  ...| no th'≢th
    with hop-tgt h' ≤?ℕ hop-tgt h
  ...| yes th'≤th = ⊥-elim (1+n≰n (≤-trans j<k (hops-nested-or-nonoverlapping (≤∧≢⇒< th'≤th th'≢th) (≤∧≢⇒< th≤j th≢j))))
  ...| no th'>th = step th≢j (lemma5-hop a' (≤-trans (hop-< h') (≤-unstep j<k)) h (≰⇒≥ th'>th) i≤th)

  lemma5 : ∀{j i k}(a : AdvPath j i)(i<k : i < k)(k≤j : k ≤′ j)
         → ∀{i₀}(b : AdvPath k i₀) → i₀ ≤ i
         → last-bef a i<k k≤j ∈AP b
  lemma5 a i<k ≤′-refl b i₀≤i = ∈AP-src
  lemma5 AdvDone i<k (≤′-step k≤j) b i₀≤i = ⊥-elim (1+n≰n (≤-unstep (≤-trans i<k (≤′⇒≤ k≤j))))
  lemma5 {k = k} (AdvThere d h a) i<k (≤′-step k≤j) b i₀≤i
       with hop-tgt h ≤?ℕ k
  ...| yes th≤k = lemma5-hop b (s≤s (≤′⇒≤ k≤j)) h th≤k (≤-trans i₀≤i (lemma1 a))
  ...| no th>k = lemma5 a i<k (≤⇒≤′ (≰⇒≥ th>k)) b i₀≤i


  -- returns the first element on path a that is greather than k
  first-aft : ∀{j i k}(a : AdvPath j i)(i≤k : i ≤′ k)(k<j : k < j) → ℕ
  first-aft {i = i} a ≤′-refl k<j = i
  first-aft AdvDone (≤′-step i≤k) k<j = ⊥-elim (1+n≰n (≤-unstep (≤-trans k<j (≤′⇒≤ i≤k))))
  first-aft {j} {i} {k} (AdvThere d h a) (≤′-step i≤k) k<j
    with hop-tgt h ≟ℕ k
  ...| yes _ = k
  ...| no th≢k
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = j
  ...| no th≥k = first-aft a (≤′-step i≤k) (≰⇒> th≥k)

  first-aft-correct : ∀{j i k}(a : AdvPath j i)(i≤k : i ≤′ k)(k<j : k < j)
                    → first-aft a i≤k k<j ∈AP a
  first-aft-correct a ≤′-refl k<j = ∈AP-tgt
  first-aft-correct AdvDone (≤′-step i≤k) k<j = ⊥-elim (1+n≰n (≤-unstep (≤-trans k<j (≤′⇒≤ i≤k))))
  first-aft-correct {j} {i} {k} (AdvThere d h a) (≤′-step i≤k) k<j
    with hop-tgt h ≟ℕ k
  ...| yes th≡k rewrite sym th≡k = step (<⇒≢ k<j) ∈AP-src
  ...| no th≢k
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = ∈AP-src
  ...| no th≥k
    with first-aft-correct a (≤′-step i≤k) (≰⇒> th≥k)
  ...| ind = step (<⇒≢ (≤-trans (s≤s (∈AP-≤ ind)) (hop-< h))) ind

  lemma5'-hop
    : ∀{j j₁ k}(h : HopFrom j)
    → hop-tgt h < k → k < j → (b : AdvPath j₁ k) → j ≤ j₁ → j ∈AP b
  lemma5'-hop {j} {j₁} h th<k k≤j b j≤j₁
    with j ≟ℕ j₁
  ...| yes refl = ∈AP-src
  ...| no j≢j₁
    with b
  ...| AdvDone = ⊥-elim (1+n≰n (≤-trans k≤j j≤j₁))
  ...| (AdvThere x hb b')
    with hop-tgt hb ≟ℕ j
  ...| yes refl = step (<⇒≢ (hop-< hb)) ∈AP-src
  ...| no tb≢j
    with hop-tgt hb ≤?ℕ j
  ...| no tb≰j = step j≢j₁ (lemma5'-hop h th<k k≤j b' (≰⇒≥ tb≰j))
  ...| yes tb≤j
    with hops-nested-or-nonoverlapping (≤-trans th<k (lemma1 b')) (≤∧≢⇒< tb≤j tb≢j)
  ...| j₁≤j rewrite ≤-antisym j≤j₁ j₁≤j = ∈AP-src


  lemma5' : ∀{j i k}(a : AdvPath j i)(i≤k : i ≤′ k)(k<j : k < j)
          → ∀{j₁}(b : AdvPath j₁ k) → j ≤ j₁
          → first-aft a i≤k k<j ∈AP b
  lemma5' a ≤′-refl k<j b j≤j₁ = ∈AP-tgt
  lemma5' AdvDone (≤′-step i≤k) k<j b j≤j₁ = ⊥-elim (1+n≰n (≤-unstep (≤-trans k<j (≤′⇒≤ i≤k))))
  lemma5' {j} {i} {k} (AdvThere d h a) (≤′-step i≤k) k<j b j≤j₁
    with hop-tgt h ≟ℕ k
  ...| yes _ = ∈AP-tgt
  ...| no th≢k
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = lemma5'-hop h (≤∧≢⇒< th≤k th≢k) k<j b j≤j₁
  ...| no th≥k = lemma5' a (≤′-step i≤k) (≰⇒> th≥k) b (≤-unstep (≤-trans (hop-< h) j≤j₁))

  ∈AP-⊕-intro-l : ∀{j k i m}
                → {a₂  : AdvPath j k}{a₁ : AdvPath k i}
                → m ∈AP a₂
                → m ∈AP (a₂ ⊕ a₁)
  ∈AP-⊕-intro-l hereTgtThere = hereTgtThere
  ∈AP-⊕-intro-l (step prog m∈a) = step prog (∈AP-⊕-intro-l m∈a)
  ∈AP-⊕-intro-l {a₁ = AdvDone} hereTgtDone = hereTgtDone
  ∈AP-⊕-intro-l {a₁ = AdvThere d h a} hereTgtDone = hereTgtThere

  ∈AP-⊕-intro-r : ∀{j k i m}
                → {a₂  : AdvPath j k}{a₁ : AdvPath k i}
                → m ∈AP a₁
                → m ∈AP (a₂ ⊕ a₁)
  ∈AP-⊕-intro-r {a₂ = AdvDone} hyp = hyp
  ∈AP-⊕-intro-r {k = k} {a₂ = AdvThere d h a} hyp =
      step (<⇒≢ (≤-trans (s≤s (∈AP-≤ hyp)) (≤-trans (s≤s (lemma1 a)) (hop-< h))))
           (∈AP-⊕-intro-r {a₂ = a} hyp)

  ∈AP-⊕-≤-r : ∀{j k i m}{a₂  : AdvPath j k}{a₁ : AdvPath k i}
            → m ∈AP (a₂ ⊕ a₁)
            → m ≤ k
            → m ∈AP a₁
  ∈AP-⊕-≤-r {a₂ = AdvDone} m∈a12 m≤k = m∈a12
  ∈AP-⊕-≤-r {a₂ = AdvThere d h a₂} hereTgtThere m≤k = ⊥-elim (1+n≰n (≤-trans (≤-trans (s≤s (lemma1 a₂)) (hop-< h)) m≤k))
  ∈AP-⊕-≤-r {a₂ = AdvThere d h a₂} (step x m∈a12) m≤k
    = ∈AP-⊕-≤-r m∈a12 m≤k

  findM : ∀ {j i₂ s₁ s₂ tgt}
          → (a₁₁ : AdvPath j s₁)
          → (a₂₁ : AdvPath j s₂)
          → (a₂₂ : AdvPath s₂ i₂)
          → (m₂ : MembershipProof s₂ tgt)
          → i₂ ≤ s₁
          → tgt ≤ s₁
          → s₁ ≤ s₂
          → ∃[ M ] (M ∈AP a₂₂ × M ∈AP mbr-proof m₂ × M ∈AP a₁₁)
  findM {s₁ = s₁} {s₂} a₁₁ a₂₁ a₂₂ m₂ i₂≤s₁ t≤s₁ s₁≤s₂
     with <-cmp s₁ s₂
  ...| tri> _ _ s₂<s₁ = ⊥-elim (<⇒≢ s₂<s₁ (sym (≤-antisym s₁≤s₂ (≤-unstep s₂<s₁))))
  ...| tri≈ _ refl _  = s₁ , ∈AP-src , ∈AP-src , ∈AP-tgt
  ...| tri< s₁<s₂ _ _ = last-bef a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₁))
                      , lemma5 a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₁)) a₂₂ i₂≤s₁
                      , lemma5 a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₁)) (mbr-proof m₂) t≤s₁
                      , last-bef-correct a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₁))

  findR : ∀{j i₁ s₁ s₂ tgt}
          → (a₁₁ : AdvPath j s₁)
          → (a₁₂ : AdvPath s₁ i₁)
          → (a₂₁ : AdvPath j s₂)
          → (m₁ : MembershipProof s₁ tgt)(m₂ : MembershipProof s₂ tgt)
          → i₁ ≤ tgt
          → tgt ≤ s₁
          → s₁ ≤ s₂ -- wlog
          → ∃[ R ] (R ∈AP mbr-proof m₁ × R ∈AP mbr-proof m₂ × R ∈AP a₁₂)
  findR {s₁ = s₁} {tgt = tgt} a₁₁ a₁₂ a₂₁ m₁ m₂ i₁≤t t≤s₁ s₁≤s₂
    with <-cmp tgt s₁
  ...| tri> _ _ s₁<t = ⊥-elim (<⇒≢ s₁<t (sym (≤-antisym t≤s₁ (≤-unstep s₁<t))))
  ...| tri≈ _ refl _ = s₁ , ∈AP-src , ∈AP-tgt , ∈AP-src
  ...| tri< t<s₁ _ _ = first-aft a₁₂ (≤⇒≤′ i₁≤t) t<s₁
                       , lemma5' a₁₂ (≤⇒≤′ i₁≤t) t<s₁ (mbr-proof m₁) ≤-refl
                       , lemma5' a₁₂ (≤⇒≤′ i₁≤t) t<s₁ (mbr-proof m₂) s₁≤s₂
                       , first-aft-correct a₁₂ (≤⇒≤′ i₁≤t) t<s₁

  -- check Figure 4 (page 12) in: https://arxiv.org/pdf/cs/0302010.pdf
  --
  -- a₁ is dashed black line
  -- a₂ is dashed gray line
  -- m₁ is thick black line
  -- m₂ is thick gray line
  -- s₁ is j
  -- s₂ is k
  -- j is n
  -- tgt is i
  evo-cr : ∀{j i₁ i₂}{t₁ t₂ : View}
          → (a₁ : AdvPath j i₁)
          → (a₂ : AdvPath j i₂)
          → rebuild a₁ t₁ j ≡ rebuild a₂ t₂ j
          → ∀{s₁ s₂ tgt}{u₁ u₂ : View}
          → (m₁ : MembershipProof s₁ tgt)(m₂ : MembershipProof s₂ tgt)
          → s₁ ∈AP a₁ → s₂ ∈AP a₂
          → s₁ ≤ s₂ -- wlog
          → i₁ ≤ tgt
          → i₂ ≤ tgt
          → rebuildMP m₁ u₁ s₁ ≡ rebuild a₁ t₁ s₁
          → rebuildMP m₂ u₂ s₂ ≡ rebuild a₂ t₂ s₂
          → HashBroke ⊎ (mbr-datum m₁ ≡ mbr-datum m₂)
  evo-cr {t₁ = t₁} {t₂} a₁ a₂ hyp {s₁} {s₂} {tgt} {u₁} {u₂}
      m₁ m₂ s₁∈a₁ s₂∈a₂ s₁≤s₂ i₁≤t i₂≤t c₁ c₂
    with ∈AP-cut a₁ s₁∈a₁ | ∈AP-cut a₂ s₂∈a₂
  ...| ((a₁₁ , a₁₂) , refl) | ((a₂₁ , a₂₂) , refl)
    with lemma1 (mbr-proof m₁)
  ...| t≤s₁
  -- The first part of the proof is find some points common to three
  -- of the provided proofs. This is given in Figure 4 of Maniatis and Baker,
  -- and they are called M and R too, to help make it at least a little clear.
  -- First we find a point that belongs in a₂, m₁ and a₁.
    with findM a₁₁ a₂₁ a₂₂ m₂ (≤-trans i₂≤t t≤s₁) t≤s₁ s₁≤s₂
  ...| M , M∈a₂₂ , M∈m₂ , M∈a₁₁
  -- Next, we find a point that belongs in m₁, m₂ and a₁.
    with findR a₁₁ a₁₂ a₂₁ m₁ m₂ i₁≤t t≤s₁ s₁≤s₂
  ...| R , R∈m₁ , R∈m₂ , R∈a₁₂
  -- Now, since a₁ and a₂ rebuild to the same hash and M belongs
  -- to both these proofs, the hash for M is the same.
    with AgreeOnCommon a₁ a₂ hyp (∈AP-⊕-intro-l M∈a₁₁) (∈AP-⊕-intro-r M∈a₂₂)
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ M-a1a2
  -- Similarly, for a₂₂ and m₂
    with AgreeOnCommon a₂₂ (mbr-proof m₂) (trans (sym (rebuild-⊕ a₂₁ a₂₂ ∈AP-src)) (sym c₂)) M∈a₂₂ M∈m₂
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ M-a22m2
  -- Which brings us to: rebuild a1 M == rebuild m2 M
    with trans (trans M-a1a2 (rebuild-⊕ a₂₁ a₂₂ M∈a₂₂)) M-a22m2
  ...| M-a1m2
  -- If a1 and m2 agree on one point, they agree on all points. In particular, they
  -- agree on R!
    with ∈AP-cut (mbr-proof m₂) M∈m₂
  ...| ((m₂₁ , m₂₂) , refl)
    with trans M-a1m2 (rebuild-⊕ m₂₁ m₂₂ ∈AP-src)
  ...| M-a1m22
    with AgreeOnCommon-∈ a₁ m₂₂ (∈AP-⊕-intro-l M∈a₁₁) M-a1m22
           (∈AP-⊕-intro-r R∈a₁₂) (∈AP-⊕-≤-r R∈m₂ (≤-trans (∈AP-≤ R∈a₁₂) (∈AP-≥ M∈a₁₁)))
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ R-a1m22
    with AgreeOnCommon a₁₂ (mbr-proof m₁) (trans (sym (rebuild-⊕ a₁₁ a₁₂ ∈AP-src)) (sym c₁)) R∈a₁₂ R∈m₁
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ R-a12m1
  -- Which finally lets us argue that m1 and m2 also agree on R. Similarly, if they agree
  -- on one point they agree on all points.
    with ∈AP-cut (mbr-proof m₁) R∈m₁
  ...| ((m₁₁ , m₁₂) , refl)
    with trans (trans (trans (sym R-a1m22) (rebuild-⊕ a₁₁ a₁₂ R∈a₁₂)) R-a12m1) (rebuild-⊕ m₁₁ m₁₂ ∈AP-src)
  ...| R-m22m12
    with AgreeOnCommon-∈ m₂₂ m₁₂ (∈AP-⊕-≤-r R∈m₂ (≤-trans (∈AP-≤ R∈a₁₂) (∈AP-≥ M∈a₁₁))) R-m22m12 ∈AP-tgt ∈AP-tgt
  ...| inj₁ hb = inj₁ hb
  ...| inj₂ tgt-m22m12
    with trans (trans (rebuild-⊕ m₁₁ m₁₂ ∈AP-tgt) (sym tgt-m22m12)) (sym (rebuild-⊕ m₂₁ m₂₂ ∈AP-tgt))
  ...| tgt-m1m2
    with rebuild-tgt-lemma (mbr-proof m₁)
                       {u₁ ∪₁ (tgt , auth tgt (mbr-datum m₁) u₁) }
                   | rebuild-tgt-lemma (mbr-proof m₂)
                       {u₂ ∪₁ (tgt , auth tgt (mbr-datum m₂) u₂) }
  ...| l1 | l2
    with trans (sym l1) (trans tgt-m1m2 l2)
  ...| auths≡
    rewrite ≟ℕ-refl tgt = auth-inj-1 {tgt} {mbr-datum m₁} {mbr-datum m₂} (mbr-not-init m₁) auths≡
