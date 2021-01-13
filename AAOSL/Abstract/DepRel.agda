{- Formal verification of authenticated append-only skiplists in Agda, version 1.0.

   Copyright (c) 2021 Victor C Miraldo.
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

-- This module defines the DepRel type, which represents the class of AAOSLs we
-- consider, and proves properties about any DepRel.

module AAOSL.Abstract.DepRel where

 open import AAOSL.Lemmas
 open import AAOSL.Abstract.Hash

 -- TODO-1: make names same as paper (lvlof -> maxlvl, etc.)
 -- The important bit is that we must have a dependency relation
 -- between these indexes.
 record DepRel : Set₁ where
   field
     lvlof      : ℕ → ℕ
     lvlof-z    : lvlof 0 ≡ 0
     lvlof-s    : ∀ m → 0 < lvlof (suc m)

   HopFrom    : ℕ → Set
   HopFrom    = Fin ∘ lvlof

   field
     hop-tgt        : {m : ℕ} → HopFrom m → ℕ

     hop-tgt-inj    : {m : ℕ}{h h' : HopFrom m}
                    → hop-tgt h ≡ hop-tgt h'
                    → h ≡ h'

     hop-<    : {m : ℕ}(h : HopFrom m)
              → hop-tgt h < m

     -- This property requires that any pair of hops is either nested or
     -- non-overlapping. When nonoverlapping, one end may coincide and
     -- when nested, both ends may coincide. As a diagram,
     --
     --                          h₂
     --            ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝
     --            ∣                             ∣
     --            ∣             h₁              ∣
     --            ∣         ⌜⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⁻⌝      |
     --            |         |            |      |
     --         tgt h₂  <I  tgt h₁  ⋯     j₁     j₂
     --                                   ↑
     --                            The only option for j₁
     --                            is right here. It can be
     --                            the same as j₂ though.
     --                            For more intuition on this, check
     --                            Hops.agda
     --
     hops-nested-or-nonoverlapping : ∀{j₁ j₂}{h₁ : HopFrom j₁}{h₂ : HopFrom j₂}
       → hop-tgt h₂ < hop-tgt h₁
       → hop-tgt h₁ < j₂
       → j₁ ≤ j₂

   _≟Hop_ : {s : ℕ}(h l : HopFrom s) → Dec (h ≡ l)
   _≟Hop_ = _≟Fin_
