import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.ObjectiveCalculus
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Strict quasiconvexity of `u fₜ''(u)` on the negative-curvature interval.
The proof uses the strictly decreasing quadratic controlling its derivative,
so does not need to introduce the quadratic roots. -/

namespace EntropyConstrainedMissingMass
noncomputable section
open Set

def weightedCurvature (t : ℕ) (u : ℝ) : ℝ :=
  u * deriv (deriv (missingMassTerm t)) u

def curvatureDerivativeQuadratic (t : ℕ) (u : ℝ) : ℝ :=
  (t : ℝ) * ((t : ℝ) + 1) * u ^ 2 - 4 * (t : ℝ) * u + 2

theorem curvatureDerivativeQuadratic_strictAnti (t : ℕ) (ht : 1 ≤ t)
    {x y : ℝ} (hxy : x < y) (hy : y ≤ 2 / ((t : ℝ) + 1)) :
    curvatureDerivativeQuadratic t y < curvatureDerivativeQuadratic t x := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have ht1 : 0 < (t : ℝ) + 1 := by positivity
  have hy' := (le_div_iff₀ ht1).1 hy
  have hgap : 0 < 4 - ((t : ℝ) + 1) * (x + y) := by nlinarith
  have hprod := mul_pos (mul_pos ht0 (sub_pos.mpr hxy)) hgap
  unfold curvatureDerivativeQuadratic
  nlinarith

/-- The manuscript's interval, with its ambient open probability interval made explicit.-/
def negativeCurvatureInterval (t : ℕ) : Set ℝ :=
  {u | 0 < u ∧ u < 1 ∧ u ≤ 2 / ((t : ℝ) + 1)}

end
end EntropyConstrainedMissingMass
