module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.ProfileOperators
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylGradedPullback
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.FiniteDirectionalBridge
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.SymmetricBaseChange
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.CyclicScalarTower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! The finite profile operators are the genuine cubic-ring directional
derivative on synthesized module-valued homogeneous polynomials. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K]

def profileDirection : Fin 3 → CyclicCubicRing (BinaryRing K) (binaryCubic K) :=
  ![cyclicCoefficientHom (binaryCubic K) (binaryU K),
    cyclicCoefficientHom (binaryCubic K) (binaryV K), cyclicRoot (binaryCubic K)]

end ChoppedPlane.QWeyl
