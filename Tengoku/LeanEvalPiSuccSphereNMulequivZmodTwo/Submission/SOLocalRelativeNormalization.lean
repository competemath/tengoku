import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOLocalExtension
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SORelativeNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative normalization from circle `SO(n)` data

This is the direct adapter between the two previously separate analytic
pieces of component normalization:

* `SOLocalExtension` extends a smooth `SO(n)` homotopy prescribed on the
  standard circle to a gauge supported in its tubular neighborhood;
* `SORelativeNormalization` turns an ambient isotopy and a smooth spatial
  `SO(n)` gauge into an actual signed framed cobordism.

The only geometric input which remains here is the ambient isotopy itself and
the smooth Cartesian representative of the circle homotopy.  In particular,
no already-extended spatial gauge is assumed by the API below.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace SOLocalRelativeNormalization

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 3))
local notation "M" => Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ

/-- The endpoint sign produced after first applying the ambient move and then
the tubular extension of the prescribed circle `SO(m+2)` homotopy.-/
def endpointSign (A : SmoothAmbientIsotopy (m + 2))
    {X : FramedLevelSet (m + 2)} (S : FiberSign X)
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) :
    FiberSign ((A.pullback X).gaugeTransform
      (fun x => SOFrameGauge.toCLM
        (SOLocalExtension.extendCircleSOHomotopy R 1 x))
      (SORelativeNormalization.contDiff_endpointGauge
        (SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero))
      (fun x => SOFrameGauge.toCLM_bijective
        (SOLocalExtension.extendCircleSOHomotopy R 1 x))) :=
  SORelativeNormalization.endpointSign A S
    (SOLocalExtension.extendCircleSOHomotopy R)
    (SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero)

/-- An ambient normalization move together with circle-level `SO(m+2)` data
gives an actual signed framed cobordism.  Spatial extension of the gauge is
constructed internally.-/
def signedCobordism (A : SmoothAmbientIsotopy (m + 2))
    (X : FramedLevelSet (m + 2)) (S : FiberSign X)
    (R : ℝ → ℝ × ℝ → SOGroup (m + 2))
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × (ℝ × ℝ) => ((R p.1 p.2 : SOGroup (m + 2)) : M) i j))
    (hRzero : ∀ z, R 0 z = 1) :
    SignedFramedLevelCobordism S (endpointSign A S R hR hRzero) :=
  SORelativeNormalization.signedCobordism A X S
    (SOLocalExtension.extendCircleSOHomotopy R)
    (SOLocalExtension.contDiff_extendCircleSOHomotopy hR hRzero)
    (SOLocalExtension.extendCircleSOHomotopy_zero R hRzero)

end SOLocalRelativeNormalization
end Submission
