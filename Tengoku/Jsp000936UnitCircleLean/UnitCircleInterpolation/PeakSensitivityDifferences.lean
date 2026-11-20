/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PeakSensitivityKernel
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.RectangularDifferences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coherent cofactors and invertible differences for actual peak sensitivities

The actual quotient kernel and actual sine-product row signs prove that the
cofactor vector has one strict sign. The augmented and adjacent-difference
matrices are therefore nonsingular. No minimum or orientation assumption is used.
The connection to the derivative of the height map is a separate analytic step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ} {hn : 0 < d + 1}

/--
@isnad1 id=or.2h2v.s6.176d5328e212 from=translated src=- shape=e8f04440 vocab=ad2f2c11
-/
theorem peakSensitivity_coherent_cofactors (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) :
    (∀ i, 0 < rectangularCofactor (peakSensitivityMatrix angles hsize) i) ∨
      (∀ i, rectangularCofactor (peakSensitivityMatrix angles hsize) i < 0) := by
  exact peakSensitivity_left_relation_coherent_sign angles hsize _
    (rectangularCofactor_left_relation _)
    (rectangularCofactor_ne_zero_of_first_minor _
      (peakSensitivityMatrix_deleted_det_ne_zero angles hsize 0))

/--
@isnad1 id=ne.2h2v.s6.f6ab255964ce from=translated src=- shape=7284b08f vocab=7edbca82
-/
theorem peakSensitivity_augmented_det_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) :
    (augmentedOnesMatrix (peakSensitivityMatrix angles hsize)).det ≠ 0 :=
  augmentedOnesMatrix_det_ne_zero_of_coherent_cofactors _
    (peakSensitivity_coherent_cofactors angles hsize)

/--
@isnad1 id=ne.2h2v.s6.aa3b62ee5bd2 from=translated src=- shape=c8994cb4 vocab=2e731c50
-/
theorem peakSensitivity_adjacent_difference_det_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) :
    (adjacentRowDifferenceMatrix (peakSensitivityMatrix angles hsize)).det ≠ 0 :=
  adjacentRowDifferenceMatrix_det_ne_zero_of_coherent_cofactors _
    (peakSensitivity_coherent_cofactors angles hsize)

end

end UnitCircleInterpolation
