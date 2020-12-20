{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Unit.NonEta
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Fin
open import Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Divisibility
open import Data.List renaming (map to List-map)
open import Data.List.Properties using (∷-injective)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All renaming (map to All-map)
open import Data.List.Relation.Unary.All.Properties hiding (All-map)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Binary.Pointwise using (decidable-≡)
open import Data.Bool
open import Data.Maybe renaming (map to Maybe-map)

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core
open import Relation.Nullary

-- This module provides an injective way to encode natural numbers

module Data.Nat.Encode where

 -- Represents a list of binary digits with
 -- a leading one in reverse order.
 --
 -- 9, in binary: 1001
 --
 -- remove leading 1: 001,
 -- reverse: 100
 --
 -- as 𝔹+1: I O O ε
 --
 data 𝔹+1 : Set where
   ε  : 𝔹+1
   O_ : 𝔹+1 → 𝔹+1
   I_ : 𝔹+1 → 𝔹+1

 from𝔹+1 : 𝔹+1 → ℕ
 from𝔹+1 ε     = 1
 from𝔹+1 (O b) = 2 * from𝔹+1 b
 from𝔹+1 (I b) = suc (2 * from𝔹+1 b)

 -- Adds zero to our representation
 data 𝔹 : Set where
   z : 𝔹
   s : 𝔹+1 → 𝔹

 from𝔹 : 𝔹 → ℕ
 from𝔹 z = 0
 from𝔹 (s b) = from𝔹+1 b

 inc : 𝔹+1 → 𝔹+1
 inc ε     = O ε
 inc (O x) = I x
 inc (I x) = O (inc x)

 inc-ε-⊥ : ∀{b} → inc b ≡ ε → ⊥
 inc-ε-⊥ {ε}   ()
 inc-ε-⊥ {O b} ()
 inc-ε-⊥ {I b} ()

 to𝔹+1 : ℕ → 𝔹+1
 to𝔹+1 zero    = ε
 to𝔹+1 (suc n) = inc (to𝔹+1 n)

 to𝔹 : ℕ → 𝔹
 to𝔹 zero    = z
 to𝔹 (suc n) = s (to𝔹+1 n)

 toBitString+1 : 𝔹+1 → List Bool
 toBitString+1 ε = []
 toBitString+1 (I x) = true ∷ toBitString+1 x
 toBitString+1 (O x) = false ∷ toBitString+1 x

 toBitString : 𝔹 → List Bool
 toBitString z = []
 -- For an actual binary number as we know, we need
 -- to reverse the result of toBitString+1; for the sake of encoding
 -- a number as a list of booleans, this works just fine
 toBitString (s x) = true ∷ toBitString+1 x

 encodeℕ : ℕ → List Bool
 encodeℕ = toBitString ∘ to𝔹

 ---------------------
 -- Injectivity proofs

 O-inj : ∀{b1 b2} → O b1 ≡ O b2 → b1 ≡ b2
 O-inj refl = refl

 I-inj : ∀{b1 b2} → I b1 ≡ I b2 → b1 ≡ b2
 I-inj refl = refl

 s-inj : ∀{b1 b2} → s b1 ≡ s b2 → b1 ≡ b2
 s-inj refl = refl

 inc-inj : ∀ b1 b2 → inc b1 ≡ inc b2 → b1 ≡ b2
 inc-inj ε ε hip = refl
 inc-inj ε (I b2) hip = ⊥-elim (inc-ε-⊥ (sym (O-inj hip)))
 inc-inj (I b1) ε hip = ⊥-elim (inc-ε-⊥ (O-inj hip))
 inc-inj (O b1) (O b2) hip = cong O_ (I-inj hip)
 inc-inj (I b1) (I b2) hip = cong I_ (inc-inj b1 b2 (O-inj hip))

 to𝔹+1-inj : ∀ n m → to𝔹+1 n ≡ to𝔹+1 m → n ≡ m
 to𝔹+1-inj zero zero hip = refl
 to𝔹+1-inj zero (suc m) hip = ⊥-elim (inc-ε-⊥ (sym hip))
 to𝔹+1-inj (suc n) zero hip = ⊥-elim (inc-ε-⊥ hip)
 to𝔹+1-inj (suc n) (suc m) hip = cong suc (to𝔹+1-inj n m (inc-inj _ _ hip))

 to𝔹-inj : ∀ n m → to𝔹 n ≡ to𝔹 m → n ≡ m
 to𝔹-inj zero zero hip = refl
 to𝔹-inj (suc n) (suc m) hip = cong suc (to𝔹+1-inj n m (s-inj hip))

 toBitString+1-inj : ∀ b1 b2 → toBitString+1 b1 ≡ toBitString+1 b2
                   → b1 ≡ b2
 toBitString+1-inj ε ε hip = refl
 toBitString+1-inj (O b1) (O b2) hip
   = cong O_ (toBitString+1-inj b1 b2 (proj₂ (∷-injective hip)))
 toBitString+1-inj (I b1) (I b2) hip
   = cong I_ (toBitString+1-inj b1 b2 (proj₂ (∷-injective hip)))


 toBitString-inj : ∀ b1 b2 → toBitString b1 ≡ toBitString b2
                 → b1 ≡ b2
 toBitString-inj z z hip = refl
 toBitString-inj (s x) (s x₁) hip
   = cong s (toBitString+1-inj x x₁ (proj₂ (∷-injective hip)))

 encodeℕ-inj : ∀ n m → encodeℕ n ≡ encodeℕ m → n ≡ m
 encodeℕ-inj n m hip = to𝔹-inj n m (toBitString-inj (to𝔹 n) (to𝔹 m) hip)
