import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOFrameGauge
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.RelativeNormalizationProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Relative normalization by a smooth special-orthogonal gauge

This file closes the analytic normalization pipeline.  Starting from an actual
ambient isotopy and a smooth `SO(n)`-valued spatial family, it constructs the
endpoint framed presentation, transports the sign, and returns the fully glued
signed normalization cobordism.  If both inputs are stationary over `K`, the
whole glued cobordism is a literal product over `K`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace SORelativeNormalization

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))
local notation "F" => EuclideanSpace ℝ (Fin n)
local notation "M" => Matrix (Fin n) (Fin n) ℝ

/-- Smoothness of the endpoint gauge obtained by fixing the time parameter at
one.
@isnad1 id=contdiff.1h2v.s10.d060b751ee28 from=translated src=- shape=76f4e8e6 vocab=f9dc08be
-/
theorem contDiff_endpointGauge
    {R : ℝ → E → SOGroup n}
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j)) :
    ContDiff ℝ ∞ (fun x => SOFrameGauge.toCLM (R 1 x)) := by
  apply SOFrameGauge.contDiff_toCLM
  intro i j
  exact (hR i j).comp (contDiff_const.prodMk contDiff_id)

/-- The endpoint sign after a special-orthogonal gauge is literally the
transported ambient sign function on the unchanged zero fiber.-/
def endpointSign (A : SmoothAmbientIsotopy n) {X : FramedLevelSet n}
    (S : FiberSign X) (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j)) :
    FiberSign ((A.pullback X).gaugeTransform
      (fun x => SOFrameGauge.toCLM (R 1 x))
      (contDiff_endpointGauge hR)
      (fun x => SOFrameGauge.toCLM_bijective (R 1 x))) :=
  (A.pullbackSign S).gaugeTransform
    (fun x => SOFrameGauge.toCLM (R 1 x))
    (contDiff_endpointGauge hR)
    (fun x => SOFrameGauge.toCLM_bijective (R 1 x))

/--
@isnad1 id=eq.1h6v.s9.f1e782ef2635 from=translated src=- shape=0040870c vocab=e25c6e98
-/
@[simp] theorem endpointSign_apply (A : SmoothAmbientIsotopy n)
    {X : FramedLevelSet n} (S : FiberSign X)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (x : E) : endpointSign A S R hR x = A.pullbackSign S x :=
  rfl

/-- Actual ambient-plus-`SO(n)`-frame normalization, including the final sign
stage.-/
def signedCobordism (A : SmoothAmbientIsotopy n)
    (X : FramedLevelSet n) (S : FiberSign X)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1) :
    SignedFramedLevelCobordism S (endpointSign A S R hR) := by
  let D := SOFrameGauge.homotopy (A.pullback X) R hR hRzero
  exact SmoothAmbientIsotopy.signedNormalizationCobordism A D S
    (endpointSign A S R hR) (by
      intro x hx
      rfl)

end SORelativeNormalization
end Submission
