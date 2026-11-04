import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Minors
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.LocalHomeomorph
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.GlobalHomeomorph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unconditional topology package for the gap-difference map

This file closes the de Boor--Pinkus topology chain.  The coherent-minor
argument proves the explicit Jacobian determinant condition; the committed
inverse-function and properness arguments then promote that condition first
to a local homeomorphism and finally to the canonical global homeomorphism
statement.
-/

namespace Erdos1153.DeBoorPinkus

noncomputable section

/-- The explicit consecutive-difference Jacobian is nonsingular at every
endpoint array.-/
theorem gapDifference_jacobianDeterminantCondition
    (d : ℕ) (A B : ℝ) :
    GapDifferenceJacobianDeterminantCondition d A B := by
  intro nodes
  change (Matrix.det (fun i j =>
    gapHeightJacobianModel nodes i.succ j -
      gapHeightJacobianModel nodes i.castSucc j)) ≠ 0
  exact gapHeightJacobianModel_consecutiveDifference_det_ne_zero nodes

end

end Erdos1153.DeBoorPinkus
