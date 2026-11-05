module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.ProfileOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.PolynomialOperatorDuality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Actual excess-three matrices in finite bases of the graded cubic modules. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open Module
variable {K : Type*} [Field K]

/-- The stated critical auxiliary degree is exactly the numerical matrix crossing.-/
theorem profileLinearMatrix_criticalTwist (s : CubicProfile) (r : ℕ) :
    linearMatrixCriticalTwist (profileRows s r) (profileRows s r+3) =
      profileCriticalDegree s r := by
  simp [linearMatrixCriticalTwist, profileCriticalDegree]

end ChoppedPlane.QWeyl
