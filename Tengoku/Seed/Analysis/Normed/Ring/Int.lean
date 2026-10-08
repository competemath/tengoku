/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Ring.Lemmas

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/

public section


namespace Int

/--
@isnad1 id=eq.0h1v.s4.4673b1e5052e from=seed src=0 shape=48d08930 vocab=f6aef7b0
-/
theorem nnnorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]

/--
@isnad1 id=eq.0h1v.s4.847e3ad0bf27 from=seed src=0 shape=48d08930 vocab=98b7ebea
-/
theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnnorm, nnnorm_coe_units, NNReal.coe_one]

/--
@isnad1 id=eq.0h1v.s5.337efc7711e5 from=seed src=0 shape=fc7e9921 vocab=efead00f
-/
@[simp]
theorem nnnorm_natCast (n : ℕ) : ‖(n : ℤ)‖₊ = n :=
  Real.nnnorm_natCast _

/--
@isnad1 id=eq.0h1v.s5.8fe4f1211165 from=seed src=0 shape=fc7e9921 vocab=9c097486
-/
@[simp] lemma enorm_natCast (n : ℕ) : ‖(n : ℤ)‖ₑ = n := Real.enorm_natCast _

/--
@isnad1 id=eq.0h1v.s5.99617a476c74 from=seed src=0 shape=0b907f95 vocab=082d043f
-/
@[simp]
theorem toNat_add_toNat_neg_eq_nnnorm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add, toNat_add_toNat_neg_eq_natAbs, NNReal.natCast_natAbs]

/--
@isnad1 id=eq.0h1v.s5.556ba67386d4 from=seed src=0 shape=0b907f95 vocab=48807394
-/
@[simp]
theorem toNat_add_toNat_neg_eq_norm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using!
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)

end Int
