{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Empty
open import Data.Fin.Properties using (toℕ<n; toℕ-injective)
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.List renaming (map to List-map)
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Definitions
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

open import Relation.Binary.PropositionalEquality renaming ( [_] to Reveal[_])
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
 using (_≅_; ≅-to-≡; ≡-to-≅; _≇_)
 renaming (cong to ≅-cong; refl to ≅-refl; cong₂ to ≅-cong₂)
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Nullary.Negation using (contradiction; contraposition)
import Relation.Nullary using (¬_)
open import Function

-- This module defines the hop relation used by the original AAOSL due to Maniatis
-- and Baker, and proves various properties needed to establish it as a valid
-- DepRel, so that we can instantiate the asbtract model with it to demonstrate that
-- it is an instance of the class of AAOSLs for which we prove our properties.

module AAOSL.Hops where

 open import AAOSL.Lemmas
 open import Data.Nat.Even

 -- The level of an index is 0 for index 0,
 -- otherwise, it is one plus the number of times
 -- that two divides said index.
 --
 -- lvlOf must be marked terminating because in one branch
 -- we make recursive call on the quotient of the argument, which
 -- is not obviously smaller than that argument
 -- This is justified by proving that lvlOf is equal to lvlOfWF,
 -- which uses well-founded recursion
 {-# TERMINATING #-}
 lvlOf : ℕ → ℕ
 lvlOf 0 = 0
 lvlOf (suc n) with even? (suc n)
 ...| no  _ = 1
 ...| yes e = suc (lvlOf (quotient e))

 -- level of an index with well-founded recursion
 lvlOfWFHelp : (n : ℕ) → Acc _<_ n → ℕ
 lvlOfWFHelp 0 p = 0
 lvlOfWFHelp (suc n) (acc rs) with even? (suc n)
 ... | no _ = 1
 ... | yes (divides q eq) = suc (lvlOfWFHelp q (rs q (1+n=m*2⇒m<1+n q n eq)))

 lvlOfWF : ℕ → ℕ
 lvlOfWF n = lvlOfWFHelp n (<-wellFounded n)

 -- When looking at an index in the form 2^k * d, the level of
 -- said index is more easily defined.
 lvlOf' : ∀{n} → Pow2 n → ℕ
 lvlOf' zero          = zero
 lvlOf' (pos l _ _ _) = suc l


 -------------------------------------------
 -- Properties of lvlOf, lvlOfWF, and lvlOf'
 lvlOf≡lvlOfWFHelp : (n : ℕ) (p : Acc _<_ n) → lvlOf n ≡ lvlOfWFHelp n p
 lvlOf≡lvlOfWFHelp 0 p = refl
 lvlOf≡lvlOfWFHelp (suc n) (acc rs) with even? (suc n)
 ... | no _ = refl
 ... | yes (divides q eq) =
   cong suc (lvlOf≡lvlOfWFHelp q (rs q (1+n=m*2⇒m<1+n q n eq)))

 lvlOf≡lvlOfWF : (n : ℕ) → lvlOf n ≡ lvlOfWF n
 lvlOf≡lvlOfWF n = lvlOf≡lvlOfWFHelp n (<-wellFounded n)

 lvlOf≡lvlOf' : ∀ n → lvlOf n ≡ lvlOf' (to n)
 lvlOf≡lvlOf' n rewrite lvlOf≡lvlOfWF n = go n (<-wellFounded n)
   where
   go : (n : ℕ) (p : Acc _<_ n) → lvlOfWFHelp n p ≡ lvlOf' (to n)
   go 0 p = refl
   go (suc n) (acc rs) with even? (suc n)
   ... | no _ = refl
   ... | yes (divides q eq) with go q (rs q (1+n=m*2⇒m<1+n q n eq))
   ... | ih with to q
   ... | pos l d odd prf = cong suc ih

 lvl≥2-even : ∀ {n} → 2 ≤ lvlOf n → Even n
 lvl≥2-even {suc n} x
    with 2 ∣? (suc n)
 ...| yes prf = prf
 ...| no  prf = ⊥-elim ((≤⇒≯ x) (s≤s (s≤s z≤n)))

 lvlOfodd≡1 : ∀ n → Odd n → lvlOf n ≡ 1
 lvlOfodd≡1 0 nodd = ⊥-elim (nodd (divides zero refl))
 lvlOfodd≡1 (suc n) nodd
    with even? (suc n)
 ...| yes prf = ⊥-elim (nodd prf)
 ...| no  prf = refl

 -- We eventually need to 'undo' a level
 lvlOf-undo : ∀{j}(e : Even (suc j)) → suc (lvlOf (quotient e)) ≡ lvlOf (suc j)
 lvlOf-undo {j} e with even? (suc j)
 ...| no  abs = ⊥-elim (abs e)
 ...| yes prf rewrite even-irrelevant e prf = refl

 ∣-cmp : ∀{t u n} → (suc t * u) ∣ n → (d : suc t ∣ n) → u ∣ (quotient d)
 ∣-cmp {t} {u} {n} (divides q1 e1) (divides q2 e2)
   rewrite sym (*-assoc q1 (suc t) u)
         | *-comm q1 (suc t)
         | *-comm q2 (suc t)
         | *-assoc (suc t) q1 u
         = divides q1 (*-cancelˡ-≡ t (trans (sym e2) e1))

 ∣-0< : ∀{n t} → 0 < n → (d : suc t ∣ n) → 0 < quotient d
 ∣-0< hip (divides zero    e) = ⊥-elim (<⇒≢ hip (sym e))
 ∣-0< hip (divides (suc q) e) = s≤s z≤n

 lvlOf-mono : ∀{n} k → 0 < n → 2 ^ k ∣ n → k ≤ lvlOf n
 lvlOf-mono zero            hip prf = z≤n
 lvlOf-mono {suc n} (suc k) hip prf
   with even? (suc n)
 ...| no abs   = ⊥-elim (abs (divides (quotient prf * (2 ^ k))
                  (trans (_∣_.equality prf)
                  (trans (cong ((quotient prf) *_) (sym (*-comm (2 ^ k) 2)))
                         (sym (*-assoc (quotient prf) (2 ^ k) 2))))))
 ...| yes prf' = s≤s (lvlOf-mono {quotient prf'} k (∣-0< hip prf') (∣-cmp prf prf'))

 -- This property can be strenghtened to < if we ever need.
 lvlOf'-mono : ∀{k} d → 0 < d → k ≤ lvlOf' (to (2 ^ k * d))
 lvlOf'-mono {k} d 0<d
   with to d
 ...| pos {d} kk dd odd eq
        with (2 ^ (k + kk)) * dd ≟ (2 ^ k) * d
 ...|      no  xx = ⊥-elim (xx  ( trans (cong (_* dd) (^-distribˡ-+-* 2 k kk))
                                        (trans (*-assoc (2 ^ k) (2 ^ kk) dd)
                                               (cong (λ x → (2 ^ k) * x) (sym eq)))))
 ...|      yes xx
             with to-reduce {(2 ^ k) * d} {k + kk} {dd} (sym xx) odd
 ...|          xx1 = ≤-trans (≮⇒≥ (m+n≮m k kk))
                             (≤-trans (n≤1+n (k + kk)) -- TODO-1: easy to strengthen to <; omit this step
                                      (≤-reflexive (sym (cong lvlOf' xx1))))

 -- And a progress property about levels:
 -- These will be much easier to reason about in terms of lvlOf'
 -- as we can see in lvlOf-correct.
 lvlOf-correct : ∀{l j} → l < lvlOf j → 2 ^ l ≤ j
 lvlOf-correct {l} {j} prf
   rewrite lvlOf≡lvlOf' j
   with to j
 ...| zero              = ⊥-elim (1+n≢0 (n≤0⇒n≡0 prf))
 ...| pos l' d odd refl = 2^kd-mono (≤-unstep2 prf) (0<odd odd)

 -- lvlOf-prog states that if we have not reached 0, we landed somewhere
 -- where we can hop again at the same level.
 lvlOf-prog : ∀{l j} → 0 < j ∸ 2 ^ l → l < lvlOf j → l < lvlOf (j ∸ 2 ^ l)
 lvlOf-prog {l} {j} hip l<lvl
   rewrite lvlOf≡lvlOf' j | lvlOf≡lvlOf' (j ∸ 2 ^ l)
   with to j
 ...| zero              = ⊥-elim (1+n≰n (≤-trans l<lvl z≤n))
 ...| pos l₁ d₁ o₁ refl
   rewrite 2^ld-2l l₁ l d₁ (≤-unstep2 l<lvl)
      with l ≟ l₁
 ...| no  l≢l₁ rewrite to-2^kd l (odd-2^kd-1 (l₁ ∸ l) d₁
                                   (0<m-n (≤∧≢⇒< (≤-unstep2 l<lvl) l≢l₁))
                                   (0<odd o₁))
                     = ≤-refl
 ...| yes refl rewrite n∸n≡0 l₁ | +-comm d₁ 0
   with odd∸1-even o₁
 ...| divides q prf rewrite prf
                          | sym (*-assoc (2 ^ l₁) q 2)
                          | a*b*2-lemma (2 ^ l₁) q
                          = lvlOf'-mono {suc l₁} q (1≤m*n⇒0<n {m = 2 ^ suc l₁} hip)

 lvlOf-no-overshoot : ∀ j l → suc l < lvlOf j → 0 < j ∸ 2 ^ l
 lvlOf-no-overshoot j l hip
   rewrite lvlOf≡lvlOf' j with to j
 ...| zero           = ⊥-elim (1+n≰n (≤-trans (s≤s z≤n) hip))
 ...| pos k d o refl = 0<m-n {2 ^ k * d} {2 ^ l}
                         (<-≤-trans (2^-mono (≤-unstep2 hip))
                                    (2^kd-mono {k} {k} ≤-refl (0<odd o)))

 ---------------------------
 -- The AAOSL Structure --
 ---------------------------

 -------------------------------
 -- Hops

 -- Encoding our hops into a relation. A value of type 'H l j i'
 -- witnesses the existence of a hop from j to i at level l.
 data H : ℕ → ℕ → ℕ → Set where
   hz : ∀ x → H 0 (suc x) x
   hs : ∀ {l x y z}
      → H l x y
      → H l y z
      → suc l < lvlOf x
      → H (suc l) x z

 -----------------------------
 -- Hop's universal properties

 -- The universal property comes for free
 h-univ : ∀{l j i} → H l j i → i < j
 h-univ (hz x)      = s≤s ≤-refl
 h-univ (hs h h₁ _) = <-trans (h-univ h₁) (h-univ h)

 -- It is easy to prove there are no hops from zero
 h-from0-⊥ : ∀{l i} → H l 0 i → ⊥
 h-from0-⊥ (hs h h₁ _) = h-from0-⊥ h

 -- And it is easy to prove that i is a distance of 2 ^ l away
 -- from j.
 h-univ₂ : ∀{l i j} → H l j i → i ≡ j ∸ 2 ^ l
 h-univ₂ (hz x) = refl
 h-univ₂ (hs {l = l} {j} h₀ h₁ _)
   rewrite h-univ₂ h₀
         | h-univ₂ h₁
         | +-comm (2 ^ l) 0
         | sym (∸-+-assoc j (2 ^ l) (2 ^ l))
         = refl

 -- and vice versa.
 h-univ₁ : ∀{l i j} → H l j i → j ≡ i + 2 ^ l
 h-univ₁ (hz x) = sym (+-comm x 1)
 h-univ₁ (hs {l = l} {z = i} h₀ h₁ _)
   rewrite h-univ₁ h₀
         | h-univ₁ h₁
         | +-comm (2 ^ l) 0
         = +-assoc i (2 ^ l) (2 ^ l)

 --------------
 -- H and lvlOf

 -- A value of type H says something about the levels of their indices
 h-lvl-src : ∀{l j i} → H l j i → l < lvlOf j
 h-lvl-src (hz x)    with even? (suc x)
 ...| no  _ = s≤s z≤n
 ...| yes _ = s≤s z≤n
 h-lvl-src (hs h₀ h₁ prf) = prf

 h-lvl-tgt : ∀{l j i} → 0 < i → H l j i → l < lvlOf i
 h-lvl-tgt prf h rewrite h-univ₂ h = lvlOf-prog prf (h-lvl-src h)

 h-lvl-inj : ∀{l₁ l₂ j i} (h₁ : H l₁ j i)(h₂ : H l₂ j i) → l₁ ≡ l₂
 h-lvl-inj {i = i} h₁ h₂
   = 2^-injective (+-cancelˡ-≡ i (trans (sym (h-univ₁ h₁)) (h-univ₁ h₂)))

 -- TODO-1: document reasons for this pragma and justify it
 {-# TERMINATING #-}
 h-lvl-half : ∀{l j i y l₁} → H l j y → H l y i → H l₁ j i → lvlOf y ≡ suc l
 h-lvl-half w₀ w₁ (hz n) = ⊥-elim (1+n≰n (≤-<-trans (h-univ w₁) (h-univ w₀)))
 h-lvl-half {l}{j}{i}{y} w₀ w₁ (hs {l = l₁} {y = y₁} sh₀ sh₁ x)
   -- TODO-2: factor out a lemma to prove l₁ ≡ l and y₁ ≡ y (already exists?)
   with l₁ ≟ l
 ...| no imp
        with j ≟ i + (2 ^ l₁) + (2 ^ l₁) | j ≟ i + (2 ^ l) + (2 ^ l)
 ...|     no imp1 | _       rewrite h-univ₁ sh₁ = ⊥-elim (imp1 (h-univ₁ sh₀))
 ...|     yes _   | no imp1 rewrite h-univ₁ w₁  = ⊥-elim (imp1 (h-univ₁ w₀))
 ...|     yes j₁  | yes j₂
            with trans (sym j₂) j₁
 ...|         xx5 rewrite +-assoc i (2 ^ l)  (2 ^ l)
                        | +-assoc i (2 ^ l₁) (2 ^ l₁)
                with +-cancelˡ-≡ i xx5
 ...|             xx6 rewrite sym (+-identityʳ (2 ^ l))
                            | sym (+-identityʳ (2 ^ l₁))
                            | +-assoc (2 ^ l)  0 ((2 ^ l)  + 0)
                            | +-assoc (2 ^ l₁) 0 ((2 ^ l₁) + 0)
                            | *-comm 2 (2 ^ l)
                            | *-comm 2 (2 ^ l₁)
                              = ⊥-elim (imp (sym (2^-injective {l} {l₁} (
                                                    sym (*2-injective (2 ^ l) (2 ^ l₁) xx6)))))
 h-lvl-half {l = l}{j = j}{i = i}{y = y} w₀ w₁ (hs {l = l₁} {y = y₁} sh₀ sh₁ x)
    | yes xx1 rewrite xx1
        with y₁ ≟ y
 ...|     no  imp = ⊥-elim (imp (+-cancelʳ-≡ y₁ y (trans (sym (h-univ₁ sh₀)) (h-univ₁ w₀))))
 ...|     yes y₁≡y rewrite y₁≡y
            with w₀
 ...|         hs {l = l-1} ssh₀ ssh₁ xx rewrite sym xx1
              = h-lvl-half sh₀ sh₁ (hs sh₀ sh₁ x)
 ...|         hz y = lvlOfodd≡1 y (even-suc-odd y (lvl≥2-even {suc y} x))

 -- If a hop goes over an index, then the level of this index is strictly
 -- less than the level of the hop. The '≤' is there because
 -- l starts at zero.
 --
 -- For example, lvlOf 4 ≡ 3; the only hops that can go over 4 are
 -- those with l of 3 or higher. In fact, there is one at l ≡ 2
 -- from 4 to 0: H 2 4 0
 h-lvl-mid : ∀{l j i} → (k : ℕ) → H l j i → i < k → k < j → lvlOf k ≤ l
 h-lvl-mid k (hz x)       i<k k<j = ⊥-elim (n≮n k (<-≤-trans k<j i<k))
 h-lvl-mid {j = j} k (hs {l = l₀}{y = y} w₀ w₁ x) i<k k<j
    with <-cmp k y
 ...| tri< k<y k≢y k≯y = ≤-step (h-lvl-mid k w₁ i<k k<y)
 ...| tri> k≮y k≢y k>y = ≤-step (h-lvl-mid k w₀ k>y k<j)
 ...| tri≈ k≮y k≡y k≯y rewrite k≡y = ≤-reflexive (h-lvl-half w₀ w₁ (hs {l = l₀}{y = y} w₀ w₁ x))

 h-lvl-≤₁ : ∀{l₁ l₂ j i₁ i₂}
          → (h : H l₁ j i₁)(v : H l₂ j i₂)
          → i₂ < i₁
          → l₁ < l₂
 h-lvl-≤₁ {l₁} {l₂} {j} {i₁} {i₂} h v i₂<i₁ =
   let h-univ = h-univ₁ h
       v-univ = h-univ₁ v
       eqj    = trans (sym v-univ) h-univ
   in log-mono l₁ l₂ (n+p≡m+q∧n<m⇒q<p i₂<i₁ eqj)

 h-lvl-≤₂ : ∀{l₁ l₂ j₁ j₂ i}
          → (h : H l₁ j₁ i)(v : H l₂ j₂ i)
          → j₁ < j₂
          → l₁ < l₂
 h-lvl-≤₂ {l₁} {l₂} {j₁} {j₂} {i} h v j₂<j₁ =
    let h-univ = h-univ₁ h
        v-univ = h-univ₁ v
    in log-mono l₁ l₂ (+-cancelˡ-< i (subst (i + (2 ^ l₁) <_) v-univ (subst (_< j₂) h-univ j₂<j₁)))

 ------------------------------
 -- Correctness and Irrelevance

 h-correct : ∀ j l → l < lvlOf j → H l j (j ∸ 2 ^ l)
 h-correct (suc j) zero prf    = hz j
 h-correct (suc j) (suc l) prf
   with h-correct (suc j) l
 ...| ind with 2 ∣? (suc j)
 ...| no  _ = ⊥-elim (ss≰1 prf)
 ...| yes e with ind (≤-unstep prf)
 ...| res₀
   with h-correct (suc j ∸ 2 ^ l) l
          (lvlOf-prog {l} {suc j}
            (lvlOf-no-overshoot (suc j) l (subst (suc l <_ ) (lvlOf-undo e) prf))
            (subst (l <_) (lvlOf-undo e) (≤-unstep prf)))
 ...| res₁
   rewrite +-comm (2 ^ l) 0
         | ∸-+-assoc (suc j) (2 ^ l) (2 ^ l)
         = hs res₀ res₁ (subst (suc l <_) (lvlOf-undo e) prf)

 h-irrelevant : ∀{l i j}
   → (h₁ : H l j i)
   → (h₂ : H l j i)
   → h₁ ≡ h₂
 h-irrelevant (hz x)       (hz .x)       = refl
 h-irrelevant (hs {y = y} h₁ h₃ x) (hs {y = z} h₂ h₄ x₁)
   rewrite ≤-irrelevant x x₁
   with y ≟ z
 ...| no abs   = ⊥-elim (abs (trans (h-univ₂ h₁) (sym (h-univ₂ h₂))))
 ...| yes refl = cong₂ (λ P Q → hs P Q x₁) (h-irrelevant h₁ h₂) (h-irrelevant h₃ h₄)

 -------------------------------------------------------------------
 -- The non-overlapping property is stated in terms
 -- of subhops. The idea is that a hop is either separate
 -- from another one, or is entirely contained within the larger one.
 --
 -- Entirely contained comes from _⊆Hop_

 data _⊆Hop_ : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
             → H l₁ j₁ i₁
             → H l₂ j₂ i₂
             → Set where
   here  : ∀{l i j}(h : H l j i) → h ⊆Hop h
   left  : ∀{l₁ i₁ j₁ l₂ i₂ w j₂ }
         → (h  : H l₁ j₁ i₁)
         → (w₀ : H l₂ j₂ w)
         → (w₁ : H l₂ w i₂)
         → (p  : suc l₂ < lvlOf j₂)
         → h ⊆Hop w₀
         → h ⊆Hop (hs w₀ w₁ p)
   right : ∀{l₁ i₁ j₁ l₂ i₂ w j₂}
         → (h  : H l₁ j₁ i₁)
         → (w₀ : H l₂ j₂ w)
         → (w₁ : H l₂ w i₂)
         → (p  : suc l₂ < lvlOf j₂)
         → h ⊆Hop w₁
         → h ⊆Hop (hs w₀ w₁ p)

 ⊆Hop-refl : ∀{l₁ l₂ j i}
           → (h₁ : H l₁ j i)
           → (h₂ : H l₂ j i)
           → h₁ ⊆Hop h₂
 ⊆Hop-refl h₁ h₂ with h-lvl-inj h₁ h₂
 ...| refl rewrite h-irrelevant h₁ h₂ = here h₂

 ⊆Hop-univ : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
           → (h1 : H l₁ j₁ i₁)
           → (h2 : H l₂ j₂ i₂)
           → h1 ⊆Hop h2
           → i₂ ≤ i₁ × j₁ ≤ j₂ × l₁ ≤ l₂
 ⊆Hop-univ h1 .h1 (here .h1) = ≤-refl , ≤-refl , ≤-refl
 ⊆Hop-univ h1 (hs w₀ w₁ p) (left h1 w₀ w₁ q hip)
   with ⊆Hop-univ h1 w₀ hip
 ...| a , b , c = (≤-trans (<⇒≤ (h-univ w₁)) a) , b , ≤-step c
 ⊆Hop-univ h1 (hs w₀ w₁ p) (right h1 w₀ w₁ q hip)
   with ⊆Hop-univ h1 w₁ hip
 ...| a , b , c = a , ≤-trans b (<⇒≤ (h-univ w₀)) , ≤-step c

 ⊆Hop-univ₁ : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
            → (h1 : H l₁ j₁ i₁)
            → (h2 : H l₂ j₂ i₂)
            → h1 ⊆Hop h2
            → i₂ ≤ i₁
 ⊆Hop-univ₁ h1 h2 h1h2 = proj₁ (⊆Hop-univ h1 h2 h1h2)

 ⊆Hop-src-≤ : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
            → (h1 : H l₁ j₁ i₁)
            → (h2 : H l₂ j₂ i₂)
            → h1 ⊆Hop h2
            → j₁ ≤ j₂
 ⊆Hop-src-≤ h1 h2 h1h2 = (proj₁ ∘ proj₂) (⊆Hop-univ h1 h2 h1h2)

 -- If two hops are not strictly the same, then the level of
 -- the smaller hop is strictly smaller than the level of
 -- the bigger hop.
 --
 -- VERY IMPORTANT
 ⊆Hop-univ-lvl : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
               → (h₁ : H l₁ j₁ i₁)
               → (h₂ : H l₂ j₂ i₂)
               → h₁ ⊆Hop h₂
               → j₁ < j₂
               → l₁ < l₂
 ⊆Hop-univ-lvl {l₁}{i₁}{j₁}{l₂}{i₂}{j₂} h₁ h₂ h₁⊆Hoph₂ j₁<j₂
                = let r₁ : i₂ + (2 ^ l₁) ≤ i₁ + (2 ^ l₁)
                      r₁ = +-monoˡ-≤ (2 ^ l₁) (proj₁ (⊆Hop-univ h₁ h₂ h₁⊆Hoph₂))
                      r₂ : i₁ + (2 ^ l₁) < i₂ + (2 ^ l₂)
                      r₂ = subst₂ _<_ (h-univ₁ h₁) (h-univ₁ h₂) j₁<j₂
                  in log-mono l₁ l₂ ((+-cancelˡ-< i₂) (≤-<-trans r₁ r₂))

 hz-⊆ : ∀{l j i k}
      → (v : H l j i)
      → i ≤ k
      → k < j
      → hz k ⊆Hop v
 hz-⊆ (hz x)      i<k k<j
   rewrite ≤-antisym (≤-unstep2 k<j) i<k = here (hz x)
 hz-⊆ {k = k} (hs {y = y} v v₁ x) i<k k<j
   with k <? y
 ...| yes k<y = right (hz k) v v₁ x (hz-⊆ v₁ i<k k<y)
 ...| no  k≮y = left  (hz k) v v₁ x (hz-⊆ v (≮⇒≥ k≮y) k<j)

 ⊆Hop-inj₁ : ∀{l₁ l₂ j i₁ i₂}
           → (h : H l₁ j i₁)(v : H l₂ j i₂)
           → i₂ < i₁
           → h ⊆Hop v
 ⊆Hop-inj₁ {i₁ = i₁} h (hz x) prf
  = ⊥-elim (n≮n i₁ (<-≤-trans (h-univ h) prf))
 ⊆Hop-inj₁ {l} {j = j} {i₁ = i₁} h (hs {l = l₁} {y = y} v v₁ x) prf
   with y ≟ i₁
 ...| yes refl = left h v v₁ x (⊆Hop-refl h v)
 ...| no  y≢i₁
   with h-lvl-≤₁ h (hs v v₁ x) prf
 ...| sl≤sl₁
   with h-univ₂ h | h-univ₂ v
 ...| prf1 | prf2
    = let r : j ∸ (2 ^ l₁) ≤ j ∸ (2 ^ l)
          r = ∸-monoʳ-≤ {m = 2 ^ l} {2 ^ l₁} j (^-mono l l₁ (≤-unstep2 sl≤sl₁))
       in left h v v₁ x (⊆Hop-inj₁ h v (≤∧≢⇒< (subst₂ _≤_ (sym prf2) (sym prf1) r) y≢i₁))

 ⊆Hop-inj₂ : ∀{l₁ l₂ j₁ j₂ i}
           → (h : H l₁ j₁ i)(v : H l₂ j₂ i)
           → j₁ < j₂
           → h ⊆Hop v
 ⊆Hop-inj₂ h (hz x) prf
   = ⊥-elim (n≮n _ (<-≤-trans prf (h-univ h)))
 ⊆Hop-inj₂ {l} {j₁ = j₁} {i = i} h (hs {l = l₁} {y = y} v v₁ x) prf
   with y ≟ j₁
 ...| yes refl = right h v v₁ x (⊆Hop-refl h v₁)
 ...| no y≢j₁
   with h-lvl-≤₂ h (hs v v₁ x) prf
 ...| sl≤sl₁
   with h-univ₁ h | h-univ₁ v₁
 ...| prf1 | prf2
    = let r : i + 2 ^ l ≤ i + 2 ^ l₁
          r = +-monoʳ-≤ i (^-mono l l₁ (≤-unstep2 sl≤sl₁))
       in right h v v₁ x (⊆Hop-inj₂ h v₁ (≤∧≢⇒< (subst₂ _≤_ (sym prf1) (sym prf2) r) (y≢j₁ ∘ sym)))

 ⊆Hop-inj₃ : ∀{l₁ l₂ j₁ j₂ i₁ i₂}
           → (h : H l₁ j₁ i₁)(v : H l₂ j₂ i₂)
           → i₁ ≡ i₂ → j₁ ≡ j₂ → h ⊆Hop v
 ⊆Hop-inj₃ h v refl refl with h-lvl-inj h v
 ...| refl rewrite h-irrelevant h v = here v

 -- This datatype encodes all the possible hop situations. This makes is
 -- much easier to structure proofs talking about two hops.
 data HopStatus : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
                → H l₁ j₁ i₁
                → H l₂ j₂ i₂
                → Set where
   -- Same hop; we carry the proofs explicitly here to be able to control
   -- when to perform the rewrites.
   Same : ∀{l₁ i₁ j₁ l₂ i₂ j₂}(h₁ : H l₁ j₁ i₁)(h₂ : H l₂ j₂ i₂)
        → i₁ ≡ i₂
        → j₁ ≡ j₂
        → HopStatus h₁ h₂

   --     h₂           h₁
   -- ⌜⁻⁻⁻⁻⁻⁻⁻⌝    ⌜⁻⁻⁻⁻⁻⁻⁻⌝
   -- |       |    |       |
   -- i₂  <   j₂ ≤ i₁  <   j₁
   SepL : ∀{l₁ i₁ j₁ l₂ i₂ j₂}(h₁ : H l₁ j₁ i₁)(h₂ : H l₂ j₂ i₂)
        → j₂ ≤ i₁
        → HopStatus h₁ h₂

   --     h₁           h₂
   -- ⌜⁻⁻⁻⁻⁻⁻⁻⌝    ⌜⁻⁻⁻⁻⁻⁻⁻⌝
   -- |       |    |       |
   -- i₁  <   j₁ ≤ i₂  <   j₂
   SepR : ∀{l₁ i₁ j₁ l₂ i₂ j₂}(h₁ : H l₁ j₁ i₁)(h₂ : H l₂ j₂ i₂)
        → j₁ ≤ i₂
        → HopStatus h₁ h₂

   --             h₂
   --  ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
   --  ∣                      ∣
   --  ∣          h₁          ∣
   --  ∣      ⌜⁻⁻⁻⁻⁻⁻⁻⌝       |
   --  |      |       |       |
   --  i₂  ≤  i₁  ⋯   j₁  ≤   j₂
   SubL : ∀{l₁ i₁ j₁ l₂ i₂ j₂}(h₁ : H l₁ j₁ i₁)(h₂ : H l₂ j₂ i₂)
        → i₂ < i₁ ⊎ j₁ < j₂ -- makes sure hops differ!
        → h₁ ⊆Hop h₂
        → HopStatus h₁ h₂

   --             h₁
   --  ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
   --  ∣                      ∣
   --  ∣          h₂          ∣
   --  ∣      ⌜⁻⁻⁻⁻⁻⁻⁻⌝       |
   --  |      |       |       |
   --  i₁  ≤  i₂  ⋯   j₂  <   j₁
   SubR : ∀{l₁ i₁ j₁ l₂ i₂ j₂}(h₁ : H l₁ j₁ i₁)(h₂ : H l₂ j₂ i₂)
        → i₁ < i₂ ⊎ j₂ < j₁ -- makes sure hops differ
        → h₂ ⊆Hop h₁
        → HopStatus h₁ h₂

 -- Finally, we can prove our no-overlap property. As it turns out, it is
 -- just a special case of general non-overlapping, and therefore, it is
 -- defined as such.
 mutual
  -- Distinguish is used to understand the relation between two arbitrary hops.
  -- It is used to perform the induction step on arbitrary hops. Note how
  -- 'no-overlap' has a clause that impedes the hops from being equal.
  distinguish : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
               → (h₁ : H l₁ j₁ i₁)
               → (h₂ : H l₂ j₂ i₂)
               → HopStatus h₁ h₂
  distinguish {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h1 h2
    with <-cmp i₁ i₂
  ...| tri≈ i₁≮i₂ i₁≡i₂ i₂≮i₁
    with <-cmp j₁ j₂
  ...| tri≈ j₁≮j₂ j₁≡j₂ j₂≮j₁ = Same h1 h2 i₁≡i₂ j₁≡j₂
  ...| tri< j₁<j₂ j₁≢j₂ j₂≮j₁ rewrite i₁≡i₂ = SubL h1 h2 (inj₂ j₁<j₂) (⊆Hop-inj₂ h1 h2 j₁<j₂)
  ...| tri> j₁≮j₂ j₁≢j₂ j₂<j₁ rewrite i₁≡i₂ = SubR h1 h2 (inj₂ j₂<j₁) (⊆Hop-inj₂ h2 h1 j₂<j₁)
  distinguish {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h1 h2
     | tri< i₁<i₂ i₁≢i₂ i₂≮i₁
    with <-cmp j₁ j₂
  ...| tri≈ j₁≮j₂ j₁≡j₂ j₂≮j₁ rewrite j₁≡j₂ = SubR h1 h2 (inj₁ i₁<i₂) (⊆Hop-inj₁ h2 h1 i₁<i₂)
  ...| tri< j₁<j₂ j₁≢j₂ j₂≮j₁ with no-overlap h2 h1 i₁<i₂
  ...| inj₁ a = SepR h1 h2 a
  ...| inj₂ b = SubR h1 h2 (inj₁ i₁<i₂) b
  distinguish {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h1 h2
     | tri< i₁<i₂ i₁≢i₂ i₂≮i₁
     | tri> j₁≮j₂ j₁≢j₂ j₂<j₁ with no-overlap h2 h1 i₁<i₂
  ...| inj₁ a = SepR h1 h2 a
  ...| inj₂ b = SubR h1 h2 (inj₁ i₁<i₂) b
  distinguish {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h1 h2
     | tri> i₁≮i₂ i₁≢i₂ i₂<i₁
    with <-cmp j₁ j₂
  ...| tri≈ j₁≮j₂ j₁≡j₂ j₂≮j₁ rewrite j₁≡j₂ = SubL h1 h2 (inj₁ i₂<i₁) (⊆Hop-inj₁ h1 h2 i₂<i₁)
  ...| tri< j₁<j₂ j₁≢j₂ j₂≮j₁ with no-overlap h1 h2 i₂<i₁
  ...| inj₁ a = SepL h1 h2 a
  ...| inj₂ b = SubL h1 h2 (inj₁ i₂<i₁) b
  distinguish {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h1 h2
     | tri> i₁≮i₂ i₁≢i₂ i₂<i₁
     | tri> j₁≮j₂ j₁≢j₂ j₂<j₁ with no-overlap h1 h2 i₂<i₁
  ...| inj₁ a = SepL h1 h2 a
  ...| inj₂ b = SubL h1 h2 (inj₁ i₂<i₁) b

  no-overlap-< : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
               → (h₁ : H l₁ j₁ i₁)
               → (h₂ : H l₂ j₂ i₂)
               → i₂ < i₁
               → i₁ < j₂
               → j₁ ≤ j₂
  no-overlap-< h₁ h₂ prf hip with no-overlap h₁ h₂ prf
  ...| inj₁ imp = ⊥-elim (1+n≰n (≤-trans hip imp))
  ...| inj₂ res = ⊆Hop-src-≤ h₁ h₂ res

  -- TODO-1: rename to nocross for consistency with paper
  -- Non-overlapping is more general, as hops might be completely
  -- separate and then, naturally won't overlap.
  no-overlap : ∀{l₁ i₁ j₁ l₂ i₂ j₂}
              → (h₁ : H l₁ j₁ i₁)
              → (h₂ : H l₂ j₂ i₂)
              → i₂ < i₁ -- this ensures h₁ ≢ h₂.
              → (j₂ ≤ i₁) ⊎ (h₁ ⊆Hop h₂)

  no-overlap h  (hz x) prf = inj₁ prf
  no-overlap {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h₁ (hs {y = y} v₀ v₁ v-ok) hip
    with distinguish h₁ v₀
  ...| SepL _ _ prf      = inj₁ prf
  ...| SubL _ _ case prf = inj₂ (left h₁ v₀ v₁ v-ok prf)
  ...| Same _ _ p1 p2    = inj₂ (left h₁ v₀ v₁ v-ok (⊆Hop-inj₃ h₁ v₀ p1 p2))
  no-overlap {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h₁ (hs {y = y} v₀ v₁ v-ok) hip
     | SepR _ _ j₁≤y
    with distinguish h₁ v₁
  ...| SepL _ _ prf              = ⊥-elim (<⇒≱ (h-univ h₁) (≤-trans j₁≤y prf))
  ...| SepR _ _ prf              = ⊥-elim (n≮n i₂ (<-trans hip (<-≤-trans (h-univ h₁) prf)))
  ...| SubR _ _ (inj₁ i₁<i₂) prf = ⊥-elim (n≮n i₂ (<-trans hip i₁<i₂))
  ...| SubR _ _ (inj₂ y<j₁)  prf = ⊥-elim (n≮n j₁ (≤-<-trans j₁≤y y<j₁))
  ...| SubL _ _ case prf         = inj₂ (right h₁ v₀ v₁ v-ok prf)
  ...| Same _ _ p1 p2            = inj₂ (right h₁ v₀ v₁ v-ok (⊆Hop-inj₃ h₁ v₁ p1 p2))
  no-overlap {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h₁ (hs {y = y} v₀ v₁ v-ok) hip
     | SubR _ _ (inj₁ i₁<y)  v₀⊆h₁
    with distinguish h₁ v₁
  ...| SepL _ _ prf              = ⊥-elim (n≮n i₁ (<-≤-trans i₁<y prf))
  ...| SepR _ _ prf              = ⊥-elim (n≮n i₂ (<-≤-trans (<-trans hip (h-univ h₁)) prf))
  ...| SubR _ _ (inj₁ i₁<i₂) prf = ⊥-elim (n≮n i₂ (<-trans hip i₁<i₂))
  ...| SubR _ _ (inj₂ y<j₁)  prf = ⊥-elim (≤⇒≯ (no-overlap-< h₁ v₁ hip i₁<y) y<j₁)
  ...| SubL _ _ case prf         = inj₂ (right h₁ v₀ v₁ v-ok prf)
  ...| Same _ _ p1 p2            = inj₂ (right h₁ v₀ v₁ v-ok (⊆Hop-inj₃ h₁ v₁ p1 p2))
  no-overlap {l₁} {i₁} {j₁} {l₂} {i₂} {j₂} h₁ (hs {y = y} v₀ v₁ v-ok) hip
     -- Here is the nasty case. We have to argue why this is impossible
     -- WITHOUT resorting to 'nov h₁ (hs v₀ v₁ v-ok)', otherwise this would
     -- result in an infinite loop. Note how 'nov' doesn't pattern match
     -- on any argument.
     --
     -- Here's what this looks like:
     --
     --               (hs v₀ v₁ v-ok)
     --          ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
     --          |                   h₁  |
     --          |        ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁺⁻⁻⁻⁻⁻⁻⁻⌝
     --          |        ∣              |       ∣
     --          |   v₁   ∣          v₀  |       ∣
     --          ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁺⁻⁻⁻⁻⁻⁻⌜⁻⁻⁻⁻⁻⁻⁻⌝       |
     --          |        |      |       |       |
     --          i₂   <   i₁  ≤  y   ⋯   j₂  <   j₁
     --
     -- We can pattern match on i₁ ≟ y
     | SubR _ _ (inj₂ j₂<j₁) v₀⊆h₁
    with i₁ ≟ y
     -- And we quickly discover that if i≢y, we have a crossing between
     -- v₁ and h₁, and that's impossible.
  ...| no  i₁≢y = ⊥-elim (n≮n y (<-≤-trans (<-trans (h-univ v₀) j₂<j₁)
                                (no-overlap-< h₁ v₁ hip (≤∧≢⇒< (⊆Hop-univ₁ v₀ h₁ v₀⊆h₁) i₁≢y))))
     -- The hard part really is when i₁ ≡ y, here's how this looks like:
     --
     --            (hs v₀ v₁ v-ok)
     -- lvl l+1  ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
     --          |                |   h₁
     --          |        ⌜⁻⁻⁻⁻⁻⁻⁻⁺⁻⁻⁻⁻⁻⁻⁻⌝   lvl l₁
     --          |        ∣       |       ∣
     --          |   v₁   ∣   v₀  |       ∣
     -- lvl l    ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁺⁻⁻⁻⁻⁻⁻⁻⌝       |
     --          |        |       |       |
     --          i₂   <   i₁  ⋯   j₂  <   j₁
     --
     -- We must show that the composite hop (hs v₀ v₁ v-ok) is impossible to build
     -- to show that the crossing doesn't happen.
     --
     -- Hence, we MUST reason about the levels of the indices and eliminate 'v-ok',
     -- Which is possible with a bit of struggling about levels.
  ...| yes refl  with h-lvl-tgt (≤-trans (s≤s z≤n) hip) v₀
  ...| l≤lvli₁   with ⊆Hop-univ-lvl _ _ v₀⊆h₁ j₂<j₁
  ...| l<l₁      with h-lvl-mid i₁ (hs v₀ v₁ v-ok) hip (h-univ v₀)
  ...| lvli₁≤l+1 with h-lvl-tgt (≤-trans (s≤s z≤n) hip) h₁
  ...| l₁≤lvli₁  rewrite ≤-antisym lvli₁≤l+1 l≤lvli₁
     = ⊥-elim (n≮n _ (<-≤-trans l<l₁ (≤-unstep2 l₁≤lvli₁)))
