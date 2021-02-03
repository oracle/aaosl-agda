{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2020 Oracle and/or its affiliates.
   Licensed under the Universal Permissive License v 1.0 as shown at https://opensource.oracle.com/licenses/upl
-}
open import Data.Unit.NonEta
open import Data.Empty
open import Data.Fin using (Fin; fromℕ≤) renaming (zero to fz; suc to fs)
import      Data.Fin.Properties renaming (_≟_ to _≟Fin_)
open import Data.Sum
open import Data.Product
open import Data.Product.Properties
open import Data.Nat renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Properties
open import Data.List renaming (map to List-map)
open import Data.List.Properties using (∷-injective; length-++)
open import Data.List.Relation.Binary.Pointwise using (decidable-≡)
open import Data.List.Relation.Unary.All as List-All
open import Data.List.Relation.Unary.Any renaming (map to Any-map)
open import Data.List.Relation.Unary.Any.Properties renaming (gmap to Any-gmap)
open import Data.Bool hiding (_≤_ ; _<_)
open import Data.Maybe renaming (map to Maybe-map)

open import Function using (_∘_)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Core
open import Relation.Nullary

-- This module contains various useful lemmas

module AAOSL.Lemmas where

 -----------------------------
 -- Properties about functions

 postulate  -- valid assumption, functional extensionality
   fun-ext : ∀{a b}{A : Set a}{B : Set b}
           → {f g : A → B}
           → (∀ x → f x ≡ g x)
           → f ≡ g

 ------------------------------
 -- Properties about inequality

 ≢-pi : ∀{a}{A : Set a}{m n : A}(p q : m ≢ n) → p ≡ q
 ≢-pi p q = fun-ext {f = p} {q} (λ x → ⊥-elim (p x))

 suc-≢ : ∀ {m n} → (suc m ≢ suc n) → m ≢ n
 suc-≢ sm≢sn m≡n = sm≢sn (cong suc m≡n)

 *-cong-≢ : ∀ p {m n} → 0 < p → m ≢ n → p * m ≢ p * n
 *-cong-≢ (suc p) 0<p m≢n p*m≡p*n = m≢n (*-cancelˡ-≡ p p*m≡p*n)

 ⊥-1≡m*2 : ∀ m → 1 ≢ m * 2
 ⊥-1≡m*2 zero = λ x → <⇒≢ (s≤s z≤n) (sym x)
 ⊥-1≡m*2 (suc m) = λ x → <⇒≢ (s≤s z≤n) (suc-injective x)

 ∸-≢ : ∀{m} n → 1 ≤ n → n ≤ suc m → suc m ∸ n ≢ suc m
 ∸-≢ {m} (suc n) 1≤n (s≤s n≤sm)
   rewrite sym (+-identityʳ (suc m))
         | sym (n∸n≡0 n)
         | sym (+-∸-assoc m {n} {n} ≤-refl)
         | +-∸-comm {m} n {n} n≤sm = m≢1+m+n (m ∸ n)

 1≢a+b : ∀{a b} → 1 ≤ a → 1 ≤ b → 1 ≢ a + b
 1≢a+b (s≤s {n = a} 1≤a) (s≤s {n = b} 1≤b) abs
   rewrite +-comm a (suc b) = 1+n≢0 (sym (suc-injective abs))

 0≢a*b-magic : ∀{a b} → 0 < a → 0 < b → 0 ≢ a * b
 0≢a*b-magic {a} {b} 0<a 0<b hip
   with m*n≡0⇒m≡0∨n≡0 a (sym hip)
 ... | inj₁ x = <⇒≢ 0<a (sym x)
 ... | inj₂ y = <⇒≢ 0<b (sym y)

 -----------------------------------
 -- Injectivty of ℕ ranged functions

 *2-injective : ∀ n m → n * 2 ≡ m * 2 → m ≡ n
 *2-injective zero    zero    x = refl
 *2-injective (suc n) (suc m) x
    = cong suc (*2-injective n m (suc-injective (suc-injective x)))

 2^-injective : ∀ {n m : ℕ}
   → 2 ^ n ≡ 2 ^ m
   → n ≡ m
 2^-injective {n} {zero} 2^n≡2^0
     with (m^n≡1⇒n≡0∨m≡1 2 n 2^n≡2^0)
 ...| inj₁ m≡0 = m≡0
 2^-injective {zero} {suc m} 2^0≡2^sm
     with (m^n≡1⇒n≡0∨m≡1 2 (suc m) (sym 2^0≡2^sm))
 ...| inj₁ sm≡0 = sym sm≡0
 2^-injective {suc n} {suc m} 2^n≡2^m = cong suc (2^-injective (*-cancelˡ-≡ {2 ^ n} {2 ^ m} 1 2^n≡2^m))

 +-inj : ∀ {m n p : ℕ} → m + n ≡ m + p → n ≡ p
 +-inj {0}     {n} {p} prf = prf
 +-inj {suc m} {n} {p} prf =  +-inj (suc-injective prf)

 ∸-inj : ∀{m} o n → o ≤ m → n ≤ m → m ∸ o ≡ m ∸ n → o ≡ n
 ∸-inj {m} o n o≤m n≤m m∸o≡m∸n =
       begin
         o
       ≡⟨ sym (m∸[m∸n]≡n o≤m) ⟩
         m ∸ (m ∸ o)
       ≡⟨ cong (m ∸_) m∸o≡m∸n ⟩
         m ∸ (m ∸ n)
       ≡⟨ m∸[m∸n]≡n n≤m ⟩
         n
       ∎

 -------------------------------
 -- Properties about _≤_ and _<_

 <-≤-trans : ∀{m n o} → m < n → n ≤ o → m < o
 <-≤-trans p q = ≤-trans p q

 ≤-<-trans : ∀{m n o} → m ≤ n → n < o → m < o
 ≤-<-trans p q = ≤-trans (s≤s p) q

 ≤-unstep2 : ∀{m n} → suc m ≤ suc n → m ≤ n
 ≤-unstep2 (s≤s p) = p

 ≤-unstep : ∀{m n} → suc m ≤ n → m ≤ n
 ≤-unstep (s≤s p) = ≤-step p

 0<-suc : ∀{m} → 0 < m → ∃[ n ] (m ≡ suc n)
 0<-suc (s≤s p) = _ , refl

 1≤0-⊥ : 1 ≤ 0 → ⊥
 1≤0-⊥ ()

 -------------------------------
 -- Properties of Multiplication

 a*2-lemma : ∀ a → (a + (a + zero)) ≡ a * 2
 a*2-lemma a rewrite *-comm a 2 = refl

 *2< : ∀ (m n : ℕ)
   → m * 2 < n * 2
   → m < n
 *2< 0       0       ()
 *2< 0       (suc n) _             = s≤s z≤n
 *2< (suc m) (suc n) (s≤s (s≤s x)) = s≤s (*2< m n x)

 a*b*2-lemma : ∀ a b → a * b * 2 ≡ (a + (a + zero)) * b
 a*b*2-lemma a b rewrite *-comm (a * b) 2
                       | *-assoc 2 a b = refl

 +-*-suc' : ∀ m n → m * suc n ≡ m + n * m
 +-*-suc' m n with *-suc m n
 ...| xx rewrite *-comm n m = xx

 ----------------------------------
 -- Properties of divisibility by 2

 1+n=m*2⇒m<1+n : ∀ m n → 1 + n ≡ m * 2 → m < 1 + n
 1+n=m*2⇒m<1+n (suc zero) (suc n) eq = s≤s (s≤s z≤n)
 1+n=m*2⇒m<1+n (suc (suc m)) (suc (suc n)) eq = s≤s (<-trans ih (n<1+n (1 + n)))
   where
   eq' : 1 + n ≡ (1 + m) * 2
   eq' = +-cancelˡ-≡ 2 eq

   ih : (1 + m) < 1 + n
   ih = 1+n=m*2⇒m<1+n (1 + m) n eq'

 -------------------------------
 -- Properties of exponentiation

 1≤2^n : ∀ n → 1 ≤ (2 ^ n)
 1≤2^n 0       = s≤s z≤n
 1≤2^n (suc n) = ≤-trans (1≤2^n n) (m≤m+n (2 ^ n) ((2 ^ n) + zero))

 1<2^sucn : ∀ n → 1 < (2 ^ suc n)
 1<2^sucn n = ≤∧≢⇒< (1≤2^n (suc n))
                    (subst (λ P → 1 ≢ (2 ^ n) + P)
                      (+-comm 0 (2 ^ n))
                      (1≢a+b (1≤2^n n) (1≤2^n n)))

 pow*d>1 : ∀ k d → 0 < k → 0 < d → 1 < 2 ^ k * d
 pow*d>1 (suc k) d 0<k 0<d = *-mono-≤ (1<2^sucn k) 0<d

 2^ld-2l : ∀ l₀ l₁ d → l₁ ≤ l₀
              → (2 ^ l₀) * d ∸ 2 ^ l₁ ≡ 2 ^ l₁ * (2 ^ (l₀ ∸ l₁) * d ∸ 1)
 2^ld-2l l₀ l₁ d x rewrite *-distribˡ-∸ (2 ^ l₁) (2 ^ (l₀ ∸ l₁) * d) 1
                         | sym (*-assoc (2 ^ l₁) (2 ^ (l₀ ∸ l₁)) d)
                         | sym (^-distribˡ-+-* 2 l₁ (l₀ ∸ l₁))
                         | sym (+-∸-assoc l₁ {l₀} {l₁} x)
                         | m+n∸m≡n l₁ l₀
                         | *-identityʳ (2 ^ l₁) = refl

 -------------------------------------
 -- Monotonicity of ℕ ranged functions

 2^-mono : ∀{m n} → m < n → 2 ^ m < 2 ^ n
 2^-mono {zero} {suc zero}    x  = s≤s (s≤s z≤n)
 2^-mono {zero} {suc (suc n)} x  = +-mono-<-≤ (2^-mono {zero} {suc n} (s≤s z≤n))
                                              (m≤n+m zero (2 * 2 ^ n))
 2^-mono {suc m} {suc n} (s≤s x) = +-mono-<   (2^-mono x)
                                              (+-mono-<-≤ (2^-mono x) z≤n)

 log-mono : ∀ (l n : ℕ)
   → 2 ^ l < 2 ^ n
   → l < n
 log-mono l 0 x = ⊥-elim (<⇒≱ x (1≤2^n l))
 log-mono 0 (suc n) x = s≤s z≤n
 log-mono (suc l) (suc n) x
   rewrite a*2-lemma (2 ^ l) | a*2-lemma (2 ^ n)
   =  s≤s ((log-mono l n (*2< (2 ^ l) (2 ^ n) x)))

 ^-mono : ∀ (l n : ℕ) → l ≤ n → 2 ^ l ≤ 2 ^ n
 ^-mono zero    n    _  = 1≤2^n n
 ^-mono (suc l) zero ()
 ^-mono (suc l) (suc n) (s≤s xx)
   rewrite +-identityʳ (2 ^ l)
         | +-identityʳ (2 ^ n)
         = +-mono-≤ (^-mono l n xx)  (^-mono l n xx)

 2^kd-mono : ∀{m n d} → m ≤ n → 0 < d → 2 ^ m ≤ 2 ^ n * d
 2^kd-mono {m} {n} {d} m≤n 0<d = ≤-trans (^-mono m n m≤n) (m≤m*n (2 ^ n) 0<d)


 1≤m*n⇒0<n : ∀{m n} → 1 ≤ m * n → 0 < n
 1≤m*n⇒0<n {m} {n} 1≤m*n rewrite *-comm m n = 1≤n*m⇒0<n n m 1≤m*n
     where 1≤n*m⇒0<n : ∀ m n →  1 ≤ m * n → 0 < m
           1≤n*m⇒0<n (suc m) n 1≤m*n = s≤s z≤n

 n+p≡m+q∧n<m⇒q<p : ∀ {n p m q} → n < m → n + p ≡ m + q → q < p
 n+p≡m+q∧n<m⇒q<p {n} {p} {m} {q} n<m n+p≡m+q = +-cancelˡ-< n (subst ((n + q) <_) (sym n+p≡m+q) (+-monoˡ-< q n<m))

 -------------------
 -- Misc. Properties

 ss≰1 : ∀{n} → suc (suc n) ≰ 1
 ss≰1 (s≤s ())

 ∸-split : ∀{a b c} → c < b → b < a → a ∸ c ≡ (a ∸ b) + (b ∸ c)
 ∸-split {a} {b} {c} c<b b<a
   rewrite sym (+-∸-comm {a} (b ∸ c) {b} (<⇒≤ b<a))
         | sym (+-∸-assoc a {b} {c} (<⇒≤ c<b))
         | +-∸-comm {a} b {c} (<⇒≤ (<-trans c<b b<a))
         | m+n∸n≡m (a ∸ c) b = refl

 0<m-n : ∀{m n} → n < m → 0 < m ∸ n
 0<m-n {n = zero} (s≤s x) = s≤s x
 0<m-n {n = suc n} (s≤s x) = 0<m-n x


 2^k-is-suc : ∀ n → ∃ (λ r → 2 ^ n ≡ suc r)
 2^k-is-suc zero = 0 , refl
 2^k-is-suc (suc n) with 2^k-is-suc n
 ...| fst , snd rewrite snd
                      | +-identityʳ fst
                      | +-comm fst (suc fst) = (suc (fst + fst)) , refl

 -------------------------
 -- Properties about lists

 ∷≡[]-⊥ : ∀{a}{A : Set a}{x : A}{xs : List A}
        → _≡_ {a} {List A} (x ∷ xs) [] → ⊥
 ∷≡[]-⊥ ()

 All-pi : ∀{a}{A : Set a}{P : A → Set}
        → (∀ {x}(p₁ p₂ : P x) → p₁ ≡ p₂)
        → {xs : List A}
        → (a₁ a₂ : All P xs)
        → a₁ ≡ a₂
 All-pi P-pi [] [] = refl
 All-pi P-pi (a ∷ as) (b ∷ bs) = cong₂ _∷_ (P-pi a b) (All-pi P-pi as bs)

 _∈_ : {A : Set} → A → List A → Set
 x ∈ xs = Any (_≡_ x) xs

 witness : {A : Set}{P : A → Set}{x : A}{xs : List A}
         → x ∈ xs → All P xs → P x
 witness {x = x} {xs = []} ()
 witness {P = P } {x = x} {xh ∷ xt} (here px) all = subst P (sym px) (List-All.head all)
 witness {x = x} {xh ∷ xt} (there x∈xt) all = witness x∈xt (List-All.tail all)

 List-map-≡ : {A B : Set}
            → (f g : A → B)
            → (xs : List A)
            → (∀ x → x ∈ xs → f x ≡ g x)
            → List-map f xs ≡ List-map g xs
 List-map-≡ f g [] prf = refl
 List-map-≡ f g (x ∷ xs) prf
   = cong₂ _∷_ (prf x (here refl)) (List-map-≡ f g xs
                                     (λ x₁ prf' → prf x₁ (there prf')))

 List-map-≡-All : {A B : Set}
                → (f g : A → B)
                → (xs : List A)
                → All (λ x → f x ≡ g x) xs
                → List-map f xs ≡ List-map g xs
 List-map-≡-All f g xs hyp
   = List-map-≡ f g xs (λ x x∈xs → witness x∈xs hyp)

 nats : (n : ℕ) → List (Fin n)
 nats 0       = []
 nats (suc n) = fz ∷ List-map fs (nats n)

 nats-correct : ∀{m}(x : Fin m) → x ∈ nats m
 nats-correct {suc m} fz     = here refl
 nats-correct {suc m} (fs x) = there (Any-gmap (cong fs) (nats-correct x))

 nats-length : ∀{m} → 0 < m → 1 ≤ length (nats m)
 nats-length (s≤s prf) = s≤s z≤n

 ++-inj : ∀{a}{A : Set a}{m n o p : List A}
        → length m ≡ length n → m ++ o ≡ n ++ p
        → m ≡ n × o ≡ p
 ++-inj {m = []}     {x ∷ n} () hip
 ++-inj {m = x ∷ m}  {[]}    () hip
 ++-inj {m = []}     {[]}     lhip hip
   = refl , hip
 ++-inj {m = m ∷ ms} {n ∷ ns} lhip hip
   with ++-inj {m = ms} {ns} (suc-injective lhip) (proj₂ (∷-injective hip))
 ...| (mn , op) rewrite proj₁ (∷-injective hip)
    = cong (n ∷_) mn , op

 ++-abs : ∀{a}{A : Set a}{n : List A}(m : List A)
        → 1 ≤ length m → [] ≡ m ++ n → ⊥
 ++-abs [] ()
 ++-abs (x ∷ m) imp ()

 ++-injₕ : ∀{a}{A : Set a}{m o p : List A}
         → m ++ o ≡ m ++ p
         → o ≡ p
 ++-injₕ {m = m} {o} {p} r = proj₂ (++-inj {m = m} {m} {o} {p} refl r)
