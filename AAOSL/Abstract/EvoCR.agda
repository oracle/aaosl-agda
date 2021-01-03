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
  last-bef AdvDone i<k (≤′-step k≤j) = ⊥-elim (1+n≰n (≤-unstep (≤-trans i<k (≤′⇒≤ k≤j))))
  last-bef {k = k} (AdvThere d h a) i<k (≤′-step k≤j)
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = hop-tgt h
  ...| no th>k = last-bef a i<k (≤⇒≤′ (≰⇒≥ th>k))

  last-bef-correct : ∀{j i k}(a : AdvPath j i)(i<k : i < k)(k≤j : k ≤′ j)
                   → last-bef a i<k k≤j ∈AP a
  last-bef-correct = {!!}

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
  first-aft AdvDone (≤′-step i≤k) k<j = {!!} -- imp
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
  first-aft-correct AdvDone (≤′-step i≤k) k<j = {!!} -- imp
  first-aft-correct {j} {i} {k} (AdvThere d h a) (≤′-step i≤k) k<j
    with hop-tgt h ≟ℕ k
  ...| yes th≡k rewrite sym th≡k = step (<⇒≢ k<j) ∈AP-src
  ...| no th≢k
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = ∈AP-src
  -- need aux lemma about first-aft a < tgt a
  ...| no th≥k = step {!!} (first-aft-correct a (≤′-step i≤k) (≰⇒> th≥k))


  lemma5'-hop
    : ∀{j j₁ k}(h : HopFrom j)
    → hop-tgt h < k → k < j → (b : AdvPath j₁ k) → j ≤ j₁ → j ∈AP b
  lemma5'-hop {j} {j₁} h th<k k≤j b j≤j₁
    with j ≟ℕ j₁
  ...| yes refl = ∈AP-src
  ...| no j≢j₁
    with b
  ...| AdvDone = {!!} -- imp
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
  lemma5' AdvDone (≤′-step i≤k) k<j b j≤j₁ = {!!} -- imp
  lemma5' {j} {i} {k} (AdvThere d h a) (≤′-step i≤k) k<j b j≤j₁
    with hop-tgt h ≟ℕ k
  ...| yes _ = ∈AP-tgt
  ...| no th≢k
    with hop-tgt h ≤?ℕ k
  ...| yes th≤k = lemma5'-hop h (≤∧≢⇒< th≤k th≢k) k<j b j≤j₁
  ...| no th≥k = lemma5' a (≤′-step i≤k) (≰⇒> th≥k) b (≤-unstep (≤-trans (hop-< h) j≤j₁))





  evo-cr' : ∀{j i₁ i₂}{t₁ t₂ : View}
          → (a₁ : AdvPath j i₁)
          → (a₂ : AdvPath j i₂)
          → rebuild a₁ t₁ j ≡ rebuild a₂ t₂ j
          → ∀{s₁ s₂ tgt}{u₁ u₂ : View}
          → (m₁ : MembershipProof s₁ tgt)(m₂ : MembershipProof s₂ tgt)
          → s₁ ∈AP a₁ → s₂ ∈AP a₂
          → tgt < s₁ → s₁ < s₂ -- wlog
          → i₁ ≤ tgt
          → i₂ ≤ tgt
          → rebuildMP m₁ u₁ ≡ rebuild a₁ t₁ s₁
          → rebuildMP m₂ u₂ ≡ rebuild a₂ t₂ s₂
          → HashBroke ⊎ (mbr-datum m₁ ≡ mbr-datum m₂)
  evo-cr' {t₁ = t₁} {t₂} a₁ a₂ hyp {s₁} {s₂} {tgt} {u₁} {u₂}
      m₁ m₂ s₁∈a₁ s₂∈a₂ t<s₁ s₁<s₂ i₁≤t i₂≤t c₁ c₂
    with ∈AP-cut a₁ s₁∈a₁ | ∈AP-cut a₂ s₂∈a₂
  ...| ((a₁₁ , a₁₂) , refl) | ((a₂₂ , a₂₁) , refl)
  -- First we find a point that belongs in a₂, m₁ and a₁.
    with lemma5 a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₂)) a₂₁ {!!}
       | lemma5 a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₂)) (mbr-proof m₂) {!!}
       | last-bef-correct a₁₁ s₁<s₂ (≤⇒≤′ (lemma1 a₂₂))
  ...| M∈a₂₁ | M∈m₂ | M∈a₁₁ = {!!}
  -- Next, we find a point that belongs in m₁, m₂ and a₁.


{-
    with lemma5

  rebuild-⊕-cong
    : ∀{j i₁ i₂}{t₁ t₂ : View}
    → (a₁ : AdvPath j i₁)(a₂ : AdvPath j i₂)
    → rebuild a₁ t₁ j ≡ rebuild a₂ t₂ j
    → ∀{k}(aₖ : AdvPath k j)
    → rebuild (aₖ ⊕ a₁) t₁ k ≡ rebuild (aₖ ⊕ a₂) t₂ k
  rebuild-⊕-cong a₁ a₂ hyp aₖ
    = {!!}


  aux2 : ∀{s j i₁ i₂}{t₁ t₂}
       → (a₁ : AdvPath s i₁)
       → (a₂ : AdvPath s i₂)
       → (k  : AdvPath j s)
       → rebuild (k ⊕ a₁) t₁ s ≡ rebuild a₂ t₂ s
       → rebuild (k ⊕ a₁) t₁ j ≡ rebuild (k ⊕ a₂) t₂ j
  aux2 a₁ a₂ AdvDone hyp = hyp
  aux2 {j = j} a₁ a₂ (AdvThere dk hk k) hyp
    rewrite ≟ℕ-refl j = cong (auth j dk) {!aux2!}

-}
