/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedCell
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedMarginGeometry
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTwoRegimeMorrey
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellProducerSlice

/-!
# The small-cell regime: the slice estimate at twice the cell radius

The slice estimate of display `eq:pressure-gradient-morrey` produces, on a
backward cylinder of radius `ρ` whose closure lies in the space-time domain, a
weak spatial derivative of the pressure slice on the **half** ball of radius
`ρ / 2`.  To control a cell of radius `r` it must therefore be applied at
`ρ = 2 * r`, and this is possible exactly when the doubled cylinder still lies
in the region the hypotheses control.

That is the margin-safe regime.  For the origin carrier the controlled region is
the closed unit cylinder, so the governing condition is `r ≤ (1 - R₁) / 4`, with
a top time in the backward window of the cylinder of admissible centres; for the
symmetric carrier of the uniform route it is `3 * r ≤ R`.  A cell that misses the
carrier
contributes nothing, because the selected field vanishes there, so only cells
meeting the carrier have to be considered, and for those the margin condition is
what makes the doubled ball fit.

Cells above the margin scale are **not** reached by this argument; they belong to
the other regime and are bounded by the whole-carrier integral.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The explicit Euclidean ball of positive radius is the Euclidean norm ball.
The slice estimate states its carrier with the first, the parabolic geometry
with the second. -/
private theorem euclideanBall_eq_vec3Ball {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change x ∈ euclideanBall x₀ r ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

end CKN.Core.Step4
