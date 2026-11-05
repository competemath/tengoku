module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticKernelBinary
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticKernelGrading
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticKernelObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The actual quartic directional kernel vanishes below twice its auxiliary
homogeneous degree in every primal and dual cyclic binary profile. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K] [CharZero K]

/-- Either cyclic orientation uses its literal prescribed generator shifts.-/
def quarticProfileWeights (dual : Bool) (s : CubicProfile) : Fin 3 → ℕ :=
  if dual then dualGeneratorWeights s else generatorWeights s

end ChoppedPlane.QWeyl
