import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.BridgeLevel
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.TubeApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A genuine bridge built from the explicit tube approximation

This module feeds `tubeApproximation` into the forward bridge construction.
Unlike `chosenBridge`, the approximation is completely explicit; only the
small Sard-regular horizontal value is chosen.  The northern sheet lies in the
region where the southern plateau is the identity, so it can be compared
directly with the tube's differential frame.
-/

noncomputable section

open Set Topology.Homotopy Function
open scoped Topology unitInterval ContDiff

namespace Submission

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 3))
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))

/-! ## The plateau is invisible on the northern sheet -/

@[simp] theorem vertC_plateauAux (u : E) :
    vertC (plateauAux u) = plateauB (vertC u) := by
  simp [plateauAux, vertC, eLast]

/-! ## The northern tube level lies inside the coordinate tube -/

/-- The normal offset over a small northern horizontal value.-/
def tubeNorthOffset (y : F) : F :=
  (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • y

/-- The offset circle in the ambient tube chart.-/
def tubeOffsetCirclePoint (k : ℕ) (y : F) (θ : ℝ) : E :=
  tubeMap k θ (tubeNorthOffset y)

/-! ## The special bridge -/

/-- The offset circle pulled back through the affine bridge coordinates.-/
def tubeBridgeCirclePoint (k : ℕ) (y : F) (θ : ℝ) : E :=
  WithLp.toLp 2 fun i => (tubeOffsetCirclePoint k y θ i + 6) / 12

@[simp] theorem tubeBridgeCirclePoint_apply (k : ℕ) (y : F) (θ : ℝ)
    (i : Fin (m + 3)) :
    tubeBridgeCirclePoint k y θ i =
      (tubeOffsetCirclePoint k y θ i + 6) / 12 :=
  rfl

theorem tubeApproxAmbient_bridgeCirclePoint (k : ℕ) (y : F) (θ : ℝ) :
    tubeApproxAmbient (WithLp.ofLp (tubeBridgeCirclePoint k y θ)) =
      tubeOffsetCirclePoint k y θ := by
  apply (EuclideanSpace.equiv (Fin (m + 3)) ℝ).injective
  funext i
  change 12 * ((tubeOffsetCirclePoint k y θ i + 6) / 12) - 6 =
    tubeOffsetCirclePoint k y θ i
  ring

end Submission
