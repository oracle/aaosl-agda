{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Unit.NonEta
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Product.Properties hiding (≡-dec)
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Data.List.Properties using (∷-injective; ≡-dec)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
open import Data.Bool hiding (_<_; _≤_) renaming (_≟_ to _≟Bool_)
open import Data.Maybe renaming (map to Maybe-map)

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary

-- This module defins a type to represent hashes, functions for encoding
-- them, and properties about them

module AAOSL.Abstract.Hash where

 open import AAOSL.Lemmas

 -- We define a ByteString as a list of bits
 ByteString : Set
 ByteString = List Bool

 -- TODO-1 : Hash -> Digest (to be consistent with the paper)?  Or just comment?

 Hash : Set
 Hash = Σ ByteString (λ bs → length bs ≡ 32)

 _≟Hash_ : (h₁ h₂ : Hash) → Dec (h₁ ≡ h₂)
 (l , pl) ≟Hash (m , pm) with ≡-dec _≟Bool_ l m
 ...| yes refl = yes (cong (_,_ l) (≡-irrelevant pl pm))
 ...| no  abs  = no (abs ∘ ,-injectiveˡ)

 encodeH : Hash → ByteString
 encodeH (bs , _) = bs

 encodeH-inj : ∀ i j → encodeH i ≡ encodeH j → i ≡ j
 encodeH-inj (i , pi) (j , pj) refl = cong (_,_ i) (≡-irrelevant pi pj)

 encodeH-len : ∀{h} → length (encodeH h) ≡ 32
 encodeH-len { bs , p } = p

 encodeH-len-lemma : ∀ i j → length (encodeH i) ≡ length (encodeH j)
 encodeH-len-lemma i j = trans (encodeH-len {i}) (sym (encodeH-len {j}))

 -- This means that we can make a helper function that combines
 -- the necessary injections into one big injection
 ++b-2-inj : (h₁ h₂ : Hash){l₁ l₂ : Hash}
           → encodeH h₁ ++ encodeH l₁
              ≡ encodeH h₂ ++ encodeH l₂
           → h₁ ≡ h₂ × l₁ ≡ l₂
 ++b-2-inj h₁ h₂ {l₁} {l₂} hip
   with ++-inj {m = encodeH h₁} {n = encodeH h₂} (encodeH-len-lemma h₁ h₂) hip
 ...| hh , ll = encodeH-inj h₁ h₂ hh , encodeH-inj l₁ l₂ ll

 Collision : {A B : Set}(f : A → B)(a₁ a₂ : A) → Set
 Collision f a₁ a₂ = a₁ ≢ a₂ × f a₁ ≡ f a₂

 module WithCryptoHash
   -- A Hash function maps a bytestring into a hash.
   (hash    : ByteString → Hash)
   (hash-cr : ∀{x y} → hash x ≡ hash y → Collision hash x y ⊎ x ≡ y) where

  HashBroke : Set
  HashBroke = Σ ( ByteString × ByteString ) (λ { (x₁ , x₂) → Collision hash x₁ x₂ })

  hash-concat : List Hash  → Hash
  hash-concat l = hash (concat (List-map encodeH l))

  -- hash-concat isinjective, modulo hash collisions
  hash-concat-inj : ∀{l₁ l₂} → hash-concat l₁ ≡ hash-concat l₂ → HashBroke ⊎ l₁ ≡ l₂
  hash-concat-inj {[]} {x ∷ xs} h with hash-cr h
  ...| inj₁ col = inj₁ (([] , encodeH x ++ foldr _++_ [] (List-map encodeH xs)) , col)
  ...| inj₂ abs = ⊥-elim (++-abs (encodeH x) (subst (1 ≤_) (sym (encodeH-len {x})) (s≤s z≤n)) abs)
  hash-concat-inj {x ∷ xs} {[]} h with hash-cr h
  ...| inj₁ col = inj₁ ((encodeH x ++ foldr _++_ [] (List-map encodeH xs) , []) , col)
  ...| inj₂ abs = ⊥-elim (++-abs (encodeH x) (subst (1 ≤_) (sym (encodeH-len {x})) (s≤s z≤n)) (sym abs))
  hash-concat-inj {[]}    {[]} h = inj₂ refl
  hash-concat-inj {x ∷ xs} {y ∷ ys} h with hash-cr h
  ...| inj₁ col = inj₁ ((encodeH x ++ foldr _++_ [] (List-map encodeH xs) , encodeH y ++ foldr _++_ [] (List-map encodeH ys)) , col)
  ...| inj₂ res  with ++-inj {m = encodeH x} {n = encodeH y} (encodeH-len-lemma x y) res
  ...| xy , xsys with hash-concat-inj {l₁ = xs} {l₂ = ys} (cong hash xsys)
  ...| inj₁ hb    = inj₁ hb
  ...| inj₂ final = inj₂ (cong₂ _∷_ (encodeH-inj x y xy) final)
