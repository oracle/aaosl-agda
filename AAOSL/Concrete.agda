{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Empty
open import Data.Sum
open import Data.Fin using (Fin; toℕ ; fromℕ ; fromℕ≤)
open import Data.Fin.Properties using (toℕ<n; toℕ-injective)
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Data.List.Relation.Unary.Any
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- This module pulls in the definitions from AAOSL.Hops and uses
-- them to construct a DepRel based on the dependency relation
-- defined there, showing that this concrete AAOSL enjoys the
-- properties we have proved for abstract ones

module AAOSL.Concrete where

 open import Data.Nat.Even
 open import Data.Nat.Encode
 open import AAOSL.Lemmas
 open import AAOSL.Hops
 open import AAOSL.Abstract.Hash
 open import AAOSL.Abstract.Advancement

 ---------------------------------------------------
 -- Translating the proofs about Hops into a DepRel,
 -- as required by AAOSL.Abstract.Advancement

 getHop : ∀{j}(h : Fin (lvlOf j)) → H (toℕ h) j (j ∸ 2 ^ toℕ h)
 getHop {j} h = h-correct j (toℕ h) (toℕ<n {lvlOf j} h)

 hop-prog : {m : ℕ} (h : Fin (lvlOf m)) → m ∸ (2 ^ toℕ h) ≢ m
 hop-prog {zero} ()
 hop-prog {suc m} h = ∸-≢ (2 ^ toℕ h) (1≤2^n (toℕ h)) (lvlOf-correct (toℕ<n h))

 hop-≤ : {m : ℕ} (h : Fin (lvlOf m)) → m ∸ (2 ^ toℕ h) ≤ m
 hop-≤ {zero} ()
 hop-≤ {suc m} h = m∸n≤m (suc m) (2 ^ toℕ h)

 lvlOfsuc : ∀ m → 0 < lvlOf (suc m)
 lvlOfsuc m with even? (suc m)
 ...| yes _ = s≤s z≤n
 ...| no  _ = s≤s z≤n

 -- This proves that ℕ makes a skiplog dependency relation
 -- by connecting the indexes by their largest power of two.
 skiplog-dep-rel : DepRel
 skiplog-dep-rel = record
   { lvlof          = lvlOf
   ; lvlof-z        = refl
   ; lvlof-s        = lvlOfsuc
   ; hop-tgt        = λ {m} h → m ∸ 2 ^ toℕ h
   ; hop-tgt-inj    = λ {m} {h} {h'} prf
                    → toℕ-injective (2^-injective {toℕ h} {toℕ h'}
                                      (∸-inj (2 ^ toℕ h) (2 ^ toℕ h')
                                             (lvlOf-correct (toℕ<n h))
                                             (lvlOf-correct (toℕ<n h'))
                                      prf))
   ; hop-<         = λ h → ≤∧≢⇒< (hop-≤ h) (hop-prog h)
   ; hops-nested-or-nonoverlapping
      = λ {h₁} {h₂} {h₃} {h₄} a b
        → no-overlap-< (getHop h₃) (getHop h₄) a b
  }

 -- This, in turn, enables us to bring the abstract module into
 -- scope with everything instantiated minus the hash functions.
 module _
    (hash    : ByteString → Hash)
    (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y)
  where

  open WithAbstractDepRel hash hash-cr encodeℕ encodeℕ-inj skiplog-dep-rel
