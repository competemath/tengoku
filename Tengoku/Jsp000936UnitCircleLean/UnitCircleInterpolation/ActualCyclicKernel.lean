/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PeakQuotients
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CyclicMinors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The relation kernel and deleted minors of the actual circle peak quotients

All degree, root-count, peak-order, and sign-table inputs are discharged for
the literal positive-gap interpolants. No generic residue or orientation
hypothesis is left in these actual-family results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ} {hn : 0 < d + 1}

/--
@isnad1 id=hascycli.0h1v.s5.15ad691ff911 from=translated src=- shape=3fe288f1 vocab=89024915
-/
lemma actualPeakQuotientSpace_hasCyclicRootBound :
    HasCyclicRootBound (d - 1) (homogeneousTrigSpace (d + 1 - 2)) := by
  rw [show d + 1 - 2 = d - 1 by omega]
  exact homogeneousTrigSpace_hasCyclicRootBound _

/--
@isnad1 id=mem.2h3v.s6.691785f11593 from=translated src=- shape=fa4e05e6 vocab=43ed0a09
-/
lemma orderedPeak_mem_Ico (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) :
    orderedPeak angles hsize i ∈ Set.Ico 0 (2 * Real.pi) := by
  have h := orderedPeak_mem_Ioo angles hsize i
  exact ⟨h.1.le, h.2⟩

/-- Every nonzero relation of actual peak quotients has one coherent alternating sign.
@isnad1 id=or.4h3v.s8.0ed4b044f5ea from=translated src=- shape=cf30fa86 vocab=c9d65bd4
-/
theorem actualPeakQuotient_relation_coherent_sign (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (a : Fin (d + 1) → ℝ)
    (hrel : ∀ t, (∑ i, a i * orderedPeakQuotient angles hsize i t) = 0)
    (ha : a ≠ 0) :
    (∀ i, 0 < (-1 : ℝ) ^ i.val * a i) ∨
      (∀ i, (-1 : ℝ) ^ i.val * a i < 0) := by
  exact cyclic_relation_coherent_sign (by omega) (homogeneousTrigSpace (d + 1 - 2))
    (continuous_of_mem_homogeneousTrigSpace _) actualPeakQuotientSpace_hasCyclicRootBound
    (orderedPeakQuotient angles hsize) (orderedPeakQuotient_mem_space angles hsize)
    (orderedPeak angles hsize) (orderedPeak_strictMono angles hsize)
    (orderedPeak_mem_Ico angles hsize) (orderedPeakQuotient_diag_neg angles hsize)
    (orderedPeakQuotient_offdiag_phase_pos angles hsize) a hrel ha

/--
@isnad1 id=ne.4h4v.s8.5e2baa608c1c from=translated src=- shape=3e7fa50d vocab=39568609
-/
theorem actualPeakQuotient_relation_coeff_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (a : Fin (d + 1) → ℝ)
    (hrel : ∀ t, (∑ i, a i * orderedPeakQuotient angles hsize i t) = 0)
    (ha : a ≠ 0) : ∀ i, a i ≠ 0 := by
  rcases actualPeakQuotient_relation_coherent_sign angles hsize a hrel ha with h | h
  · intro i hi
    have := h i
    simp [hi] at this
  · intro i hi
    have := h i
    simp [hi] at this

/--
@isnad1 id=eq.4h4v.s8.8dd3169b4911 from=translated src=- shape=4acae64a vocab=39568609
-/
theorem actualPeakQuotient_relation_eq_zero_of_missing_coeff
    (angles : CyclicAngles (d + 1) hn) (hsize : 2 ≤ d + 1)
    (a : Fin (d + 1) → ℝ)
    (hrel : ∀ t, (∑ i, a i * orderedPeakQuotient angles hsize i t) = 0)
    (omitted : Fin (d + 1)) (hmissing : a omitted = 0) : a = 0 := by
  by_contra ha
  exact actualPeakQuotient_relation_coeff_ne_zero angles hsize a hrel ha omitted hmissing

/-- Deleting any one actual peak quotient leaves `d` independent functions.
@isnad1 id=linearin.2h3v.s6.97aedebf7b02 from=translated src=- shape=24735aee vocab=25be366e
-/
theorem actualPeakQuotient_deleted_linearIndependent
    (angles : CyclicAngles (d + 1) hn) (hsize : 2 ≤ d + 1) (omitted : Fin (d + 1)) :
    LinearIndependent ℝ
      (fun i : Fin d => orderedPeakQuotient angles hsize (omitted.succAbove i)) := by
  exact cyclic_deleted_linearIndependent (by omega) (homogeneousTrigSpace (d + 1 - 2))
    (continuous_of_mem_homogeneousTrigSpace _) actualPeakQuotientSpace_hasCyclicRootBound
    (orderedPeakQuotient angles hsize) (orderedPeakQuotient_mem_space angles hsize)
    (orderedPeak angles hsize) (orderedPeak_strictMono angles hsize)
    (orderedPeak_mem_Ico angles hsize) (orderedPeakQuotient_diag_neg angles hsize)
    (orderedPeakQuotient_offdiag_phase_pos angles hsize) omitted

/-- All deleted evaluation matrices of the actual quotients are nonsingular,
at any `d` distinct canonical angles, including an evaluation at `π`.
@isnad1 id=ne.4h4v.s7.5353ad92d1a0 from=translated src=- shape=2c9c8b0c vocab=38b5cc45
-/
theorem actualPeakQuotient_deleted_evaluation_det_ne_zero
    (angles : CyclicAngles (d + 1) hn) (hsize : 2 ≤ d + 1) (omitted : Fin (d + 1))
    (x : Fin d → ℝ) (hxinj : Function.Injective x)
    (hxbound : ∀ j, x j ∈ Set.Ico 0 (2 * Real.pi)) :
    ((cyclicEvaluationMatrix (orderedPeakQuotient angles hsize) x).submatrix
      omitted.succAbove id).det ≠ 0 := by
  exact cyclicEvaluationMatrix_deleted_row_det_ne_zero (by omega)
    (homogeneousTrigSpace (d + 1 - 2))
    (continuous_of_mem_homogeneousTrigSpace _) actualPeakQuotientSpace_hasCyclicRootBound
    (orderedPeakQuotient angles hsize) (orderedPeakQuotient_mem_space angles hsize)
    (orderedPeak angles hsize) (orderedPeak_strictMono angles hsize)
    (orderedPeak_mem_Ico angles hsize) (orderedPeakQuotient_diag_neg angles hsize)
    (orderedPeakQuotient_offdiag_phase_pos angles hsize) omitted x hxinj hxbound

end

end UnitCircleInterpolation
