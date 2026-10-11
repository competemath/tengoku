/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.NewtonianDerivativeLocalLp

/-!
# Potential Local Lp Kernel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- The Newtonian kernel truncated to the ball of radius `R` about the origin. -/
def truncatedNewtonianPotentialKernel (R : ℝ) : Vec3 → ℝ := fun z =>
  if ‖z‖ < R then newtonianKernel z else 0

/-- The truncated Newtonian kernel is measurable. -/
theorem measurable_truncatedNewtonianPotentialKernel (R : ℝ) :
    Measurable (truncatedNewtonianPotentialKernel R) := by
  unfold truncatedNewtonianPotentialKernel
  have hk : Measurable (newtonianKernel : Vec3 → ℝ) := by
    unfold newtonianKernel
    have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact measurable_const.div (measurable_const.mul hnorm)
  exact hk.piecewise (measurableSet_lt measurable_norm measurable_const) measurable_const

end CKN.Foundation.Euclidean
