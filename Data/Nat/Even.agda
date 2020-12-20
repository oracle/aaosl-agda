{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Nat.Divisibility
open import Data.Nat.Properties

open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
 using (_≅_; ≅-to-≡; ≡-to-≅; _≇_)
 renaming (cong to ≅-cong; refl to ≅-refl; cong₂ to ≅-cong₂)

open import Function

-- This module proves a number of properties about even numbers.
-- We borrow some things from Data.Nat.Divisibility but specialize most
-- of them to divisibility-by-2.
module Data.Nat.Even where

 open import AAOSL.Lemmas

 Even : ℕ → Set
 Even n = 2 ∣ n

 even? : (n : ℕ) → Dec (Even n)
 even? n = 2 ∣? n

 Odd : ℕ → Set
 Odd = ¬_ ∘ Even

 even-irrelevant : ∀{n}(p q : Even n) → p ≡ q
 even-irrelevant (divides q₁ e₁) (divides q₂ e₂)
   with *2-injective q₁ q₂ (trans (sym e₁) e₂)
 ...| refl = cong (divides q₁) (≡-irrelevant e₁ e₂)

 --------------------------------------------------
 -- Properties about stepping and unstepping 'Even'

 even-unstep : ∀ k → Even (2 + k) → Even k
 even-unstep k (divides (suc q) e) = divides q (suc-injective (suc-injective e))

 even-step : ∀ k → Even k → Even (2 + k)
 even-step k (divides q₁ eq) = divides (1 + q₁) (cong (suc ∘ suc) eq)

 -----------------------------
 -- Properties of Even and Odd

 mutual
  even-odd-suc : ∀ k → Even k → Odd (suc k)
  even-odd-suc zero    x (divides q e) = ⊥-1≡m*2 q e
  even-odd-suc (suc k) x x₁            = even-suc-odd (suc k) x₁ x

  even-suc-odd : ∀ k → Even (suc k) → Odd k
  even-suc-odd zero    (divides q e) x₁ = ⊥-1≡m*2 q e
  even-suc-odd (suc k) x             x₁ = even-odd-suc k (even-unstep k x) x₁

 mutual
  odd-suc-suc : ∀ k → Odd k → Even (suc k)
  odd-suc-suc zero x = ⊥-elim (x (divides 0 refl))
  odd-suc-suc (suc k) x = even-step k (odd-pred-even (suc k) x)

  odd-pred-even : ∀ k → Odd k → Even (pred k)
  odd-pred-even zero x = ⊥-elim (x (divides 0 refl))
  odd-pred-even (suc k) x with even? k
  ...| no imp = ⊥-elim (x (odd-suc-suc k imp))
  ...| yes prf = prf

 -----------------------------
 -- Properties of Even and _*_

 *-preserve-even : ∀ k d → Even k → Even (k * d)
 *-preserve-even k d = ∣m⇒∣m*n d

 -----------------------------
 -- Properties of Even and _≤_

 even>0⇒>1 : ∀ {k} → 0 < k → Even k → 1 < k
 even>0⇒>1 {0}           ()
 even>0⇒>1 {1}           0<k e = ⊥-elim ((even-odd-suc 0 (divides 0 refl)) e)
 even>0⇒>1 {suc (suc k)} (s≤s z≤n) _ = s≤s (s≤s z≤n)

 0<odd : ∀{d} → Odd d → 0 < d
 0<odd {zero}  imp = ⊥-elim (imp (divides zero refl))
 0<odd {suc d} _   = s≤s z≤n

 -----------------------------
 -- Properties of Even and _∸_

 even∸1-odd : ∀ {k} → 1 < k → Even k → Odd (k ∸ 1)
 even∸1-odd {suc zero} 1<k ek = λ x → contradiction refl (<⇒≢ 1<k)
 even∸1-odd {suc (suc k)} 1<k ek = λ x → even-suc-odd (suc k) ek x

 odd∸1-even : ∀ {k} → Odd k → Even (k ∸ 1)
 odd∸1-even {zero} ok = ⊥-elim (ok (divides 0 refl))
 odd∸1-even {suc zero} ok = divides 0 refl
 odd∸1-even {suc (suc k)} ok = odd-pred-even (suc (suc k)) ok

 -----------------------------
 -- Properties of Even and _^_

 even-2^k : ∀ {k} → 0 < k → Even (2 ^ k)
 even-2^k {suc k} x = *-preserve-even 2 (2 ^ k) (divides 1 refl)

 odd-2^kd-1 : ∀ k d → 0 < k → 0 < d → ¬ Even (2 ^ k * d ∸ 1)
 odd-2^kd-1 k d 0<k 0<d x
   = even∸1-odd {2 ^ k * d} (pow*d>1 k d 0<k 0<d)
                            (*-preserve-even (2 ^ k) d (even-2^k 0<k))
                            x

 ----------------------------------------------------------------
 -- Every natural number can be viewed as a power of two times
 -- an odd number. We can witness that conversion in the from and
 -- to functions below.
 data Pow2 : ℕ → Set where
   zero : Pow2 zero
   pos  : ∀ {n} l d → Odd d → n ≡ 2 ^ l * d → Pow2 n

 pos-cong : ∀{n₁ n₂} (p : n₁ ≡ n₂)
          → ∀{d₁ d₂} (q : d₁ ≡ d₂)
          → (o₁ : Odd d₁)(o₂ : Odd d₂)
          → ∀{m} (r₁ : m ≡ 2 ^ n₁ * d₁) (r₂ : m ≡ 2 ^ n₂ * d₂)
          → pos n₁ d₁ o₁ r₁ ≡ pos n₂ d₂ o₂ r₂
 pos-cong {n₁ = n} refl {d₁ = d} refl o₁ o₂ r₁ r₂
   = cong₂ (pos n d) (fun-ext (λ x → ⊥-elim (o₁ x))) (≡-irrelevant r₁ r₂)

 -- One must mark this as terminating. The recursive call
 -- is made with 'quotient prf', and although we know it is
 -- strictly smaller than (suc n), Agda can't infer it.
 {-# TERMINATING #-}
 to : (n : ℕ) → Pow2 n
 to 0       = zero
 to (suc n) with even? (suc n)
 ...| no  odd = pos 0 (suc n) odd (cong suc (+-comm 0 n))
 ...| yes prf with to (quotient prf)
 ...| zero             = ⊥-elim (1+n≢0 (_∣_.equality prf))
 ...| pos l d odd prf' = pos (suc l) d odd
                         (trans (_∣_.equality prf)
                         (trans (cong (λ x → x * 2) prf')
                                (a*b*2-lemma (2 ^ l) d)))

 -- Converting from a Pow2 is trivial, since we kept the
 -- original number there.
 from : ∀{n} → Pow2 n → ℕ
 from zero              = zero
 from (pos {n} _ _ _ _) = n

 -- From and To form an isomorphism
 -- TODO-1: Document and justify this pragma
 {-# TERMINATING #-}
 from-to-iso : ∀ n → from (to n) ≡ n
 from-to-iso zero = refl
 from-to-iso (suc n) with even? (suc n)
 ...| no  odd = refl
 ...| yes prf with to (quotient prf)
 ...| zero             = ⊥-elim (1+n≢0 (_∣_.equality prf))
 ...| pos l d odd prf' = refl

 --------------------------------
 -- Properties of to and equality

 inj-to : ∀ {m n} → m ≡ n → to m ≅ to n
 inj-to refl = ≅-refl

 to-inj :  ∀ {m n} → to m ≇ to n → m ≢ n
 to-inj x x₁ = x (inj-to x₁)

 ---------------------------
 -- Uniqueness of 2^k*d form

 2^kd-≢-d : ∀{k d₁ d₂}
          → d₁ ≢ d₂
          → 2 ^ k * d₁ ≢ 2 ^ k * d₂
 2^kd-≢-d {k} hip abs with 2^k-is-suc k
 ...| r , prf rewrite prf = hip (*-cancelˡ-≡ r abs)

 2^kd-≢-k : ∀{k₁ k₂ d₁ d₂}
             → k₁ ≢ k₂
             → Odd d₁ → Odd d₂
             → 2 ^ k₁ * d₁ ≢ 2 ^ k₂ * d₂
 2^kd-≢-k {zero} {zero} {d₁} {d₂} k₁≢k₂ o₁ o₂ e₁≡e₂ = k₁≢k₂ refl
 2^kd-≢-k {zero} {suc k₂} {d₁} {d₂} k₁≢k₂ o₁ o₂ e₁≡e₂
   rewrite +-identityʳ d₁
         | *-assoc 2 (2 ^ k₂) d₂
         | *-comm 2 (2 ^ k₂ * d₂) = o₁ (divides (2 ^ k₂ * d₂) e₁≡e₂)
 2^kd-≢-k {suc k₁} {zero} {d₁} {d₂} k₁≢k₂ o₁ o₂ e₁≡e₂
   rewrite +-identityʳ d₂
         | *-assoc 2 (2 ^ k₁) d₁
         | *-comm 2 (2 ^ k₁ * d₁) = o₂ (divides (2 ^ k₁ * d₁) (sym e₁≡e₂))
 2^kd-≢-k {suc k₁} {suc k₂} {d₁} {d₂} k₁≢k₂ o₁ o₂ e₁≡e₂
   rewrite  *-assoc 2 (2 ^ k₁) d₁
         |  *-assoc 2 (2 ^ k₂) d₂ = *-cong-≢ 2 (s≤s z≤n) (2^kd-≢-k (suc-≢ k₁≢k₂) o₁ o₂) e₁≡e₂

 ----------------------
 -- Correctness of 'to'

 -- The trick to 2^kd is to use heterogeneous equality first.
 -- The problem stems from the type of arguments of pos depending
 -- on each other. Agda has trouble understanding that the different
 -- ways to write 'n' are all equal. Hence, we abstract that away.
 to-2^kd-≅ : ∀{n d} k → (o : Odd d)(p : n ≡ 2 ^ k * d)
           → to n ≅ pos k d o refl
 to-2^kd-≅ {n} {d} k o p with to n
 ...| zero = ⊥-elim (0≢a*b-magic (1≤2^n k) (0<odd o) p)
 to-2^kd-≅ {n} {d} k o p
    | pos k₀ d₀ o₀ p₀
   with k ≟ k₀
 ...| no abs = ⊥-elim (2^kd-≢-k abs o o₀ (trans (sym p) p₀))
 ...| yes refl
   with d ≟ d₀
 ...| no abs = ⊥-elim (2^kd-≢-d {k₀} abs (trans (sym p) p₀))
 to-2^kd-≅ {n} {d} .k₀ o p
    | pos k₀ d₀ o₀ p₀ | yes refl | yes refl
   rewrite fun-ext {f = o} {o₀} (λ x → ⊥-elim (o x)) | p
   with p₀
 ...| refl = ≅-refl

 -- And then, Agda is happy to understand it is equal after all.
 to-2^kd : ∀{d} k → (o : Odd d) → to (2 ^ k * d) ≡ pos k d o refl
 to-2^kd {d} k p = ≅-to-≡ (to-2^kd-≅ k p refl)

 to-reduce : ∀ {m k d}
           → (mprf : m ≡ (2 ^ k) * d)
           → (od : Odd d)
           → to m ≡ pos k d od mprf
 to-reduce {m} {k} {d} refl od = to-2^kd k od
