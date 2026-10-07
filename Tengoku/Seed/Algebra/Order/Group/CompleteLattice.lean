/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Group.OrderIso
public import Tengoku.Seed.Order.ConditionallyCompleteLattice.Indexed

/-!
# Distributivity of group operations over supremum/infimum
-/

public section

open Set

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G] [Nonempty ι] {f : ι → G}

section Right
variable [MulRightMono G]

/--
@isnad1 id=eq.1h4v.s7.a903187e58d0 from=seed src=0 shape=cfe14451 vocab=056b3324
-/
@[to_additive]
lemma ciSup_mul (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_ciSup hf

/--
@isnad1 id=eq.1h4v.s6.d1aee71d0773 from=seed src=0 shape=cfe14451 vocab=fdb21c0e
-/
@[to_additive]
lemma ciSup_div (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, ciSup_mul hf]

/--
@isnad1 id=eq.1h4v.s7.05d192ac0d15 from=seed src=0 shape=cfe14451 vocab=bb421424
-/
@[to_additive]
lemma ciInf_mul (hf : BddBelow (range f)) (a : G) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  (OrderIso.mulRight a).map_ciInf hf

/--
@isnad1 id=eq.1h4v.s6.8c0d732be1c3 from=seed src=0 shape=cfe14451 vocab=3a7ab016
-/
@[to_additive]
lemma ciInf_div (hf : BddBelow (range f)) (a : G) : (⨅ i, f i) / a = ⨅ i, f i / a := by
  simp only [div_eq_mul_inv, ciInf_mul hf]

end Right

section Left
variable [MulLeftMono G]

/--
@isnad1 id=eq.1h4v.s7.d6ec74136324 from=seed src=0 shape=91c51810 vocab=d0de6ba6
-/
@[to_additive]
lemma mul_ciSup (hf : BddAbove (range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_ciSup hf

/--
@isnad1 id=eq.1h4v.s7.a1cc5e241ec4 from=seed src=0 shape=91c51810 vocab=33e36d90
-/
@[to_additive]
lemma mul_ciInf (hf : BddBelow (range f)) (a : G) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  (OrderIso.mulLeft a).map_ciInf hf

end Left
