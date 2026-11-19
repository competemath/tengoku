/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.Definitions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary phase and Bohr-set lemmas

These are the first checked ingredients for Section 3 of the paper.
-/

open MeasureTheory Set

namespace QuadraticCarleson

/--
@isnad1 id=eq.0h1v.s3.d61a7e76d519 from=translated src=- shape=0cfb200e vocab=9855f1a5
-/
@[simp]
theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 := by
  simpa [phase] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * s)

/--
@isnad1 id=eq.0h2v.s4.f3e500a9a553 from=translated src=- shape=0438c7a3 vocab=3351fac0
-/
theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/--
@isnad1 id=le.0h1v.s3.79e3aab4f4b0 from=translated src=- shape=8a62b088 vocab=214a13e9
-/
theorem torusNorm_nonneg (x : ℝ) : 0 ≤ torusNorm x := by
  rw [torusNorm]
  exact le_min (Int.fract_nonneg x) (sub_nonneg.mpr (Int.fract_lt_one x).le)

/--
@isnad1 id=le.0h1v.s4.a4fd4f81f17d from=translated src=- shape=45b89831 vocab=59ad29d8
-/
theorem torusNorm_le_half (x : ℝ) : torusNorm x ≤ 1 / 2 := by
  rw [torusNorm]
  rcases le_total (Int.fract x) (1 / 2 : ℝ) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

/--
@isnad1 id=eq.0h2v.s4.efb6baae31f7 from=translated src=- shape=1dc88c11 vocab=dc94ee0b
-/
@[simp]
theorem torusNorm_add_int (x : ℝ) (z : ℤ) : torusNorm (x + z) = torusNorm x := by
  simp [torusNorm, Int.fract_add_intCast]

/--
@isnad1 id=measurab.0h0v.s2.d3716de574f5 from=translated src=- shape=e3d48bcb vocab=db8e51eb
-/
theorem measurable_torusNorm : Measurable torusNorm := by
  change Measurable (fun x : ℝ => min (Int.fract x) (1 - Int.fract x))
  exact measurable_fract.min (measurable_const.sub measurable_fract)

/--
@isnad1 id=le.0h2v.s5.1656ea7c3dfe from=translated src=- shape=e89cd402 vocab=eb9238dd
-/
theorem bohrSet_subset_Ico (k : ℕ) (ρ : ℝ) :
    bohrSet k ρ ⊆ Ico (1 / 4 : ℝ) (1 / 2 : ℝ) := by
  intro x hx
  exact hx.1

/--
@isnad1 id=measurab.0h2v.s3.eadd761f1db7 from=translated src=- shape=a51c7acb vocab=7ac66f3c
-/
theorem measurableSet_bohrSet (k : ℕ) (ρ : ℝ) : MeasurableSet (bohrSet k ρ) := by
  rw [bohrSet]
  exact measurableSet_Ico.inter <|
    measurableSet_le (measurable_torusNorm.comp (measurable_const.mul measurable_id))
      measurable_const

end QuadraticCarleson
