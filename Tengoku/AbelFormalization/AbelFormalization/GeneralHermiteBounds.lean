import Tengoku.AbelFormalization.AbelFormalization.HermiteCoefficientBounds
import Tengoku.AbelFormalization.AbelFormalization.NormalizedPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Hermite coefficient bounds for arbitrary separated radii

The contour radius may be any positive `R`; the nodes may lie in any closed
disk of radius `b < R`.  The gap `R-b` keeps the node polynomial nonzero on
the contour, and compactness gives coefficient bounds uniform in all nodes.
-/

noncomputable section

open Set Metric Polynomial

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/-- Closed node polydisk and contour circle, with independent radii.-/
def generalHermiteContourParameters (b R : ℝ) : Set ((ι → ℂ) × ℂ) :=
  {p | (∀ i, ‖p.1 i‖ ≤ b) ∧ ‖p.2‖ = R}

omit [Fintype ι] in
/--
@isnad1 id=iscompac.0h3v.s5.26ff6dce1273 from=translated src=- shape=84884db5 vocab=bb07e2a3
-/
theorem isCompact_generalHermiteContourParameters (b R : ℝ) :
    IsCompact (generalHermiteContourParameters (ι := ι) b R) := by
  have hn : IsCompact {δ : ι → ℂ | ∀ i, δ i ∈ closedBall 0 b} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall 0 b
  have hn' : IsCompact {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ b} := by
    simpa only [mem_closedBall, dist_zero_right] using hn
  have hs : IsCompact {ζ : ℂ | ‖ζ‖ = R} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) R
  exact hn'.prod hs

end AbelFormalization
