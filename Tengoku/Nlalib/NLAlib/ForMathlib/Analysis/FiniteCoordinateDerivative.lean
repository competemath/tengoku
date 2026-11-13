import Tengoku.Seed.Analysis.Normed.Operator.ContinuousLinearMap
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.Algebra.BigOperators.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate decomposition of a finite-dimensional continuous linear map
-/

noncomputable section
open scoped BigOperators

namespace ContinuousLinearMap

variable {κ F : Type*} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous real linear map on a finite coordinate space is the sum of
its coordinate projections multiplied by its values on the coordinate vectors.-/
theorem sum_proj_smulRight (L : (κ → ℝ) →L[ℝ] F) :
    (∑ j, (proj (R := ℝ) (φ := fun _ : κ => ℝ) j).smulRight (L (Pi.single j 1))) = L := by
  ext x
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum, map_smul]

end ContinuousLinearMap
