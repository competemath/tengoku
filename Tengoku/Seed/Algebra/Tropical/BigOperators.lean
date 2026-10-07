/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Data.List.MinMax
public import Tengoku.Seed.Algebra.Tropical.Basic
public import Tengoku.Seed.Order.ConditionallyCompleteLattice.Finset
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-!

# Tropicalization of finitary operations

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferable order/lattice structure, to support
`Real`, `Rat`, `EReal`, and others (`ERat` is not yet defined).

Minima over `List α` are defined as producing a value in `WithTop α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/

public section

variable {R S : Type*}

open Tropical Finset

/--
@isnad1 id=eq.0h2v.s5.15e5b5f28c2f from=seed src=0 shape=da709f9b vocab=4518bb46
-/
theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map trop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

/--
@isnad1 id=eq.0h2v.s4.609854e2cf0d from=seed src=0 shape=da709f9b vocab=8215323f
-/
theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)

/--
@isnad1 id=eq.0h4v.s5.b6276f3f34a3 from=seed src=0 shape=c4279869 vocab=2df26178
-/
theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i ∈ s, f i) = ∏ i ∈ s, trop (f i) := by
  convert! Multiset.trop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/--
@isnad1 id=eq.0h2v.s5.0041845b1a4a from=seed src=0 shape=6cf4381c vocab=1a08677c
-/
theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.prod = List.sum (l.map untrop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

/--
@isnad1 id=eq.0h2v.s4.16b453b74d8b from=seed src=0 shape=6cf4381c vocab=af7fd281
-/
theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)

/--
@isnad1 id=eq.0h4v.s5.31d0ec7f1bda from=seed src=0 shape=35e51400 vocab=c9942fa1
-/
theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i ∈ s, f i) = ∑ i ∈ s, untrop (f i) := by
  convert! Multiset.untrop_prod (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/--
@isnad1 id=eq.0h2v.s6.27004c937e1e from=seed src=0 shape=230cb955 vocab=10c800a9
-/
theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ WithTop.some)) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [List.minimum_cons, ← IH]

/--
@isnad1 id=eq.0h2v.s5.40a22f0bcb3c from=seed src=0 shape=0ea849fd vocab=a775e195
-/
theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp [← IH]

/--
@isnad1 id=eq.0h4v.s6.37d7dece200c from=seed src=0 shape=eba3bbc3 vocab=98bff215
-/
theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i ∈ s, trop (f i) := by
  convert! Multiset.trop_inf (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply]
  rfl

/--
@isnad1 id=eq.0h4v.s6.418a491e82e5 from=seed src=0 shape=8c7f4a0c vocab=1d5fd5e6
-/
theorem trop_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (sInf (f '' s)) = ∑ i ∈ s, trop (f i) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, trop_top]
  rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, s.trop_inf]

/--
@isnad1 id=eq.0h3v.s6.100b01185d8d from=seed src=0 shape=1d3cbc5b vocab=9d3822ad
-/
theorem trop_iInf [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, trop_sInf_image]

/--
@isnad1 id=eq.0h2v.s5.3421802ddeb1 from=seed src=0 shape=46007bd0 vocab=ad1a3a8f
-/
theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.sum = Multiset.inf (s.map untrop) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons s x IH => simp only [sum_cons, untrop_add, map_cons, inf_cons, ← IH]

/--
@isnad1 id=eq.0h4v.s6.443237ceab40 from=seed src=0 shape=e8f357c1 vocab=02f6b23a
-/
theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i ∈ s, f i) = s.inf (untrop ∘ f) := by
  convert! Multiset.untrop_sum (s.val.map f)
  simp only [Multiset.map_map, Function.comp_apply, inf_def]

/--
@isnad1 id=eq.0h4v.s6.4dda6176644a from=seed src=0 shape=e19119b1 vocab=1fef6a53
-/
theorem untrop_sum_eq_sInf_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = sInf (untrop ∘ f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.sInf_empty, untrop_zero]
  · rw [← inf'_eq_csInf_image _ h, inf'_eq_inf, Finset.untrop_sum']

/--
@isnad1 id=eq.0h3v.s6.a54442183dc1 from=seed src=0 shape=0e534bef vocab=c2b9d857
-/
theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [iInf, ← Set.image_univ, ← coe_univ, untrop_sum_eq_sInf_image, Function.comp_def]

/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices!
@isnad1 id=eq.0h4v.s7.012efdb22083 from=seed src=0 shape=9ab17471 vocab=7975dc04
-/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i ∈ s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← _root_.untrop_sum] using (sum_attach _ _).symm
