/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Algebra.Exponential

/-! # The exponential map from selfadjoint to unitary
In this file, we establish various properties related to the map
`fun a ↦ NormedSpace.exp ℂ A (I • a)` between the subtypes `selfAdjoint A` and `unitary A`.

## TODO

* Show that any exponential unitary is path-connected in `unitary A` to `1 : unitary A`.
* Prove any unitary whose distance to `1 : unitary A` is less than `1` can be expressed as an
  exponential unitary.
* A unitary is in the path component of `1` if and only if it is a finite product of exponential
  unitaries.
-/

@[expose] public section

open NormedSpace -- For `NormedSpace.exp`.

section Star

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

open Complex

/-- The map from the selfadjoint real subspace to the unitary group. This map only makes sense
over ℂ. -/
@[simps]
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A :=
  ⟨exp ((I • a.val) : A),
      let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
      exp_mem_unitary_of_mem_skewAdjoint (a.prop.smul_mem_skewAdjoint conj_I)⟩

open selfAdjoint

/--
@isnad1 id=eq.0h1v.s9.75ff4d923607 from=seed src=0 shape=f0147523 vocab=2a0a8424
-/
@[simp]
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1 := by
  ext
  simp

/--
@isnad1 id=continuo.0h1v.s8.3130637af589 from=seed src=0 shape=0ec3d04d vocab=353ab296
-/
@[fun_prop]
lemma selfAdjoint.continuous_expUnitary : Continuous (expUnitary : selfAdjoint A → unitary A) := by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  let +nondep : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  fun_prop

/--
@isnad1 id=eq.1h3v.s10.e45caef50548 from=seed src=0 shape=25524675 vocab=97678f73
-/
theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  simpa only [Subtype.ext_iff, expUnitary_coe, AddSubgroup.coe_add, smul_add] using!
    exp_add_of_commute ((h.smul_left I).smul_right I)

/--
@isnad1 id=commute.1h3v.s9.a5fb38f694a5 from=seed src=0 shape=0eb439e5 vocab=bb4b15df
-/
theorem Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    Commute (expUnitary a) (expUnitary b) := by
  rw [Commute, SemiconjBy, ← h.expUnitary_add, ← h.symm.expUnitary_add, add_comm]

end Star
