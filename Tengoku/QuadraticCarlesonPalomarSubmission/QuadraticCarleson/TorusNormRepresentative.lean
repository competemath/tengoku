/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.BohrIntersection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The paper's distance-to-integers norm

The fractional-part formula already used by the Bohr-set proofs agrees with
the minimum of the distances to all integers. On the paper's chosen
representative interval `[-1/2, 1/2)`, it is the ordinary absolute value.
-/

open Set

namespace QuadraticCarleson

set_option autoImplicit false

/-- The torus norm equals absolute value on the representative interval
specified in the paper's notation section.
@isnad1 id=eq.1h1v.s6.9cf8d98b3cbe from=translated src=- shape=5a0a3d8f vocab=8252a105
-/
theorem torusNorm_eq_abs_of_mem_Ico {x : ℝ}
    (hx : x ∈ Ico (-1 / 2 : ℝ) (1 / 2 : ℝ)) : torusNorm x = |x| := by
  by_cases hx0 : 0 ≤ x
  · have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0, by linarith [hx.2]⟩
    rw [torusNorm, hfract, min_eq_left (by linarith [hx.2]), abs_of_nonneg hx0]
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have hfloor : ⌊x⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr (by
      constructor <;> norm_num <;> linarith [hx.1])
    have hfract : Int.fract x = x + 1 := by simp [Int.fract, hfloor]
    rw [torusNorm, hfract, min_eq_right (by linarith [hx.1]), abs_of_neg hxneg]
    ring

/-- Distance to the nearest integer is bounded by distance to zero.
@isnad1 id=le.0h1v.s3.0eb3b215c946 from=translated src=- shape=dc093f10 vocab=2c7b3d19
-/
theorem torusNorm_le_abs (x : ℝ) : torusNorm x ≤ |x| := by
  by_cases hx : |x| < 1 / 2
  · exact (torusNorm_eq_abs_of_mem_Ico
      ⟨by linarith [(abs_lt.mp hx).1], (abs_lt.mp hx).2⟩).le
  · exact (torusNorm_le_half x).trans (le_of_not_gt hx)

/--
@isnad1 id=eq.0h2v.s4.7ef21b611fe1 from=translated src=- shape=1dc88c11 vocab=a82bf3ab
-/
@[simp]
theorem torusNorm_sub_int (x : ℝ) (z : ℤ) : torusNorm (x - z) = torusNorm x := by
  simp [torusNorm, Int.fract_sub_intCast]

/-- The fractional-part formula is a lower bound for distance to every integer.
@isnad1 id=le.0h2v.s4.01bb0368a174 from=translated src=- shape=5027d4b1 vocab=e2145089
-/
theorem torusNorm_le_abs_sub_int (x : ℝ) (z : ℤ) : torusNorm x ≤ |x - z| := by
  simpa using torusNorm_le_abs (x - z)

/-- One integer attains the torus norm, so this is a minimum, not merely an infimum.
@isnad1 id=ex.0h1v.s4.464138742c41 from=translated src=- shape=0e9685c1 vocab=52397bf2
-/
theorem exists_int_abs_sub_eq_torusNorm (x : ℝ) : ∃ z : ℤ, |x - z| = torusNorm x := by
  obtain ⟨z, hz⟩ := exists_int_abs_sub_le_of_torusNorm_le (le_refl (torusNorm x))
  exact ⟨z, le_antisymm hz (torusNorm_le_abs_sub_int x z)⟩

/-- Exact agreement with the paper's definition `min_{z ∈ ℤ} |x-z|`.
@isnad1 id=isleast.0h1v.s4.06596c89df6c from=translated src=- shape=6f9755c7 vocab=dba31200
-/
theorem torusNorm_isLeast_integerDistances (x : ℝ) :
    IsLeast (range (fun z : ℤ ↦ |x - z|)) (torusNorm x) := by
  refine ⟨exists_int_abs_sub_eq_torusNorm x, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact torusNorm_le_abs_sub_int x z

/-- An infimum formulation of the distance-to-integers identity.
@isnad1 id=eq.0h1v.s4.211dde3d4c25 from=translated src=- shape=9efbc462 vocab=f8990e99
-/
theorem torusNorm_eq_iInf_abs_sub_int (x : ℝ) :
    torusNorm x = ⨅ z : ℤ, |x - z| := by
  exact (torusNorm_isLeast_integerDistances x).csInf_eq.symm

end QuadraticCarleson
