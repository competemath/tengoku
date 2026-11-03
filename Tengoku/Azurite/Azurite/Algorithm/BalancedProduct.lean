/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.Algebra.BigOperators.Group.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
## Balanced products

`balancedProduct l` multiplies a list by pairing adjacent elements until one remains: a balanced
binary tree of products.  For big numbers (or polynomials) of similar size this keeps every
multiplication balanced, so the subquadratic multiplication algorithms apply at every level,
whereas a left fold multiplies a growing accumulator by small factors.  The tree is driven by a
fuel of `l.length` pairing rounds — more than the `⌈log₂ l.length⌉` needed — with a fold as the
fallback, so the result is the product for every fuel (`balancedProduct_eq_prod`, in any monoid).
The additive twins `addAdjacentPairs`, `sumTree`, `balancedSum` serve types whose addition is as
costly as multiplication, such as rationals.
-/

namespace Azurite

/-- Multiply adjacent pairs; an odd last element is kept.-/
def mulAdjacentPairs {α : Type*} [Mul α] : List α → List α
  | x :: y :: rest => (x * y) :: mulAdjacentPairs rest
  | l => l

/-- The product of a list by `fuel` rounds of pairing; a left fold finishes if the fuel runs
out.-/
def prodTree {α : Type*} [Mul α] [One α] : Nat → List α → α
  | 0, l => l.foldl (· * ·) 1
  | fuel + 1, l =>
    match l with
    | [] => 1
    | [x] => x
    | _ => prodTree fuel (mulAdjacentPairs l)

/-- **The product of a list by a balanced tree** of pairwise products.-/
def balancedProduct {α : Type*} [Mul α] [One α] (l : List α) : α := prodTree l.length l

variable {α : Type*} [Monoid α]

/--
@isnad1 id=eq.0h2v.s5.8bbffe26cc82 from=translated src=- shape=660825d4 vocab=d34b12f8
-/
theorem mulAdjacentPairs_prod : ∀ l : List α, (mulAdjacentPairs l).prod = l.prod
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [mulAdjacentPairs, List.prod_cons, mulAdjacentPairs_prod rest, List.prod_cons,
      List.prod_cons, mul_assoc]

/--
@isnad1 id=eq.0h3v.s6.126de1f9edc4 from=translated src=- shape=d8570093 vocab=2ddb6907
-/
theorem foldl_mul_eq_mul_prod (l : List α) (acc : α) : l.foldl (· * ·) acc = acc * l.prod := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/--
@isnad1 id=eq.0h3v.s5.f66e5963a208 from=translated src=- shape=adf70b88 vocab=f53de47d
-/
theorem prodTree_eq_prod : ∀ (fuel : ℕ) (l : List α), prodTree fuel l = l.prod
  | 0, l => by rw [prodTree, foldl_mul_eq_mul_prod, one_mul]
  | _ + 1, [] => by simp [prodTree]
  | _ + 1, [x] => by simp [prodTree]
  | fuel + 1, x :: y :: rest => by
    show prodTree fuel (mulAdjacentPairs (x :: y :: rest)) = _
    rw [prodTree_eq_prod fuel, mulAdjacentPairs_prod]

/-- **The balanced product is the product**, for every fuel and in any monoid.
@isnad1 id=eq.0h2v.s5.775c81e32976 from=translated src=- shape=40e80979 vocab=0d933de1
-/
theorem balancedProduct_eq_prod (l : List α) : balancedProduct l = l.prod :=
  prodTree_eq_prod _ _

/-! ### The additive twins -/

/-- Add adjacent pairs; an odd last element is kept.-/
def addAdjacentPairs {β : Type*} [Add β] : List β → List β
  | x :: y :: rest => (x + y) :: addAdjacentPairs rest
  | l => l

/-- The sum of a list by `fuel` rounds of pairing; a left fold finishes if the fuel runs out.-/
def sumTree {β : Type*} [Add β] [Zero β] : Nat → List β → β
  | 0, l => l.foldl (· + ·) 0
  | fuel + 1, l =>
    match l with
    | [] => 0
    | [x] => x
    | _ => sumTree fuel (addAdjacentPairs l)

/-- **The sum of a list by a balanced tree** of pairwise sums.-/
def balancedSum {β : Type*} [Add β] [Zero β] (l : List β) : β := sumTree l.length l

variable {β : Type*} [AddMonoid β]

/--
@isnad1 id=eq.0h2v.s5.ae0b182657c1 from=translated src=- shape=660825d4 vocab=8fb907c2
-/
theorem addAdjacentPairs_sum : ∀ l : List β, (addAdjacentPairs l).sum = l.sum
  | [] => rfl
  | [_] => rfl
  | x :: y :: rest => by
    rw [addAdjacentPairs, List.sum_cons, addAdjacentPairs_sum rest, List.sum_cons, List.sum_cons,
      add_assoc]

/--
@isnad1 id=eq.0h3v.s5.601fb3b68ca4 from=translated src=- shape=d8570093 vocab=dabcbc50
-/
theorem foldl_add_eq_add_sum (l : List β) (acc : β) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/--
@isnad1 id=eq.0h3v.s5.238619c5b55f from=translated src=- shape=adf70b88 vocab=aa4bf907
-/
theorem sumTree_eq_sum : ∀ (fuel : ℕ) (l : List β), sumTree fuel l = l.sum
  | 0, l => by rw [sumTree, foldl_add_eq_add_sum, zero_add]
  | _ + 1, [] => by simp [sumTree]
  | _ + 1, [x] => by simp [sumTree]
  | fuel + 1, x :: y :: rest => by
    show sumTree fuel (addAdjacentPairs (x :: y :: rest)) = _
    rw [sumTree_eq_sum fuel, addAdjacentPairs_sum]

/-- **The balanced sum is the sum**, for every fuel and in any additive monoid.
@isnad1 id=eq.0h2v.s5.1c94b42a19b3 from=translated src=- shape=40e80979 vocab=8c4e58aa
-/
theorem balancedSum_eq_sum (l : List β) : balancedSum l = l.sum :=
  sumTree_eq_sum _ _

end Azurite
