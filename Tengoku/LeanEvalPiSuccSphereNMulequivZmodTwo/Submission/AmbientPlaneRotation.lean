import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SO2FrameGauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A concrete ambient plane-rotation isotopy

The explicit `SO(2)` block used for frame gauges also gives a global ambient
isotopy.  In ambient dimension `m+2`, this file constructs the path from the
identity to rotation through a prescribed angle in the first coordinate
plane.  Together with affine isotopies, this supplies the elementary rigid
positioning moves needed after an orbit circle has been rounded.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff RealInnerProductSpace

namespace Submission
namespace SmoothAmbientIsotopy

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (m + 2))

/-- Collar-flat angle used by the ambient rotation.-/
def planeRotationAngle (θ s : ℝ) : ℝ := normRamp s * θ

/-- Ambient rotation in the first coordinate plane.-/
def planeRotation (θ : ℝ) : SmoothAmbientIsotopy (m + 1) where
  forward s x := SO2FrameGauge.rotate (planeRotationAngle θ s) x
  inverse s x := SO2FrameGauge.rotate (-(planeRotationAngle θ s)) x
  forward_smooth := by
    have hangle : ContDiff ℝ ∞ (fun p : ℝ × E => normRamp p.1 * θ) :=
      (contDiff_normRamp.comp contDiff_fst).mul contDiff_const
    have hpair : ContDiff ℝ ∞
        (fun p : ℝ × E => (normRamp p.1 * θ, p.2)) :=
      hangle.prodMk contDiff_snd
    simpa [Function.comp_def, planeRotationAngle] using
      SO2FrameGauge.contDiff_rotate.comp hpair
  inverse_smooth := by
    have hangle : ContDiff ℝ ∞ (fun p : ℝ × E => -(normRamp p.1 * θ)) :=
      ((contDiff_normRamp.comp contDiff_fst).mul contDiff_const).neg
    have hpair : ContDiff ℝ ∞
        (fun p : ℝ × E => (-(normRamp p.1 * θ), p.2)) :=
      hangle.prodMk contDiff_snd
    simpa [Function.comp_def, planeRotationAngle] using
      SO2FrameGauge.contDiff_rotate.comp hpair
  forward_zero := by
    funext x
    rw [planeRotationAngle,
      normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num), zero_mul,
      SO2FrameGauge.rotate_zero]
    rfl
  left_inv := by
    intro s hs x
    exact SO2FrameGauge.rotate_neg_apply (planeRotationAngle θ s) x
  right_inv := by
    intro s hs x
    exact SO2FrameGauge.rotate_apply_neg (planeRotationAngle θ s) x
  inverse_fderiv_surjective := by
    intro s hs x
    have hfd : fderiv ℝ
        (fun y : E => SO2FrameGauge.rotate (-(planeRotationAngle θ s)) y) x =
        SO2FrameGauge.rotateCLM (-(planeRotationAngle θ s)) :=
      (SO2FrameGauge.rotateCLM (-(planeRotationAngle θ s))).hasFDerivAt.fderiv
    rw [hfd]
    exact (SO2FrameGauge.rotateCLM_bijective _).2

/--
@isnad1 id=eq.0h4v.s6.1c0cb50633a4 from=translated src=- shape=b3eb181e vocab=0d8794c1
-/
@[simp] theorem planeRotation_forward (θ s : ℝ) (x : E) :
    (planeRotation θ).forward s x =
      SO2FrameGauge.rotate (planeRotationAngle θ s) x :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.5b5337877c53 from=translated src=- shape=a8eef8e7 vocab=82d38244
-/
@[simp] theorem planeRotation_inverse (θ s : ℝ) (x : E) :
    (planeRotation θ).inverse s x =
      SO2FrameGauge.rotate (-(planeRotationAngle θ s)) x :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.a3e3388de080 from=translated src=- shape=1d838610 vocab=1cd10b2a
-/
@[simp] theorem planeRotationAngle_zero (θ : ℝ) :
    planeRotationAngle θ 0 = 0 := by
  rw [planeRotationAngle,
    normRamp_of_le_quarter (show (0 : ℝ) ≤ 1 / 4 by norm_num), zero_mul]

/--
@isnad1 id=eq.0h1v.s3.528d6f6b53ad from=translated src=- shape=1fa26838 vocab=1cd10b2a
-/
@[simp] theorem planeRotationAngle_one (θ : ℝ) :
    planeRotationAngle θ 1 = θ := by
  rw [planeRotationAngle,
    normRamp_of_three_quarter_le (show (3 / 4 : ℝ) ≤ 1 by norm_num), one_mul]

/--
@isnad1 id=eq.0h3v.s6.18f3fa19b914 from=translated src=- shape=8463f2b6 vocab=7bca74af
-/
@[simp] theorem planeRotation_forward_endpoint (θ : ℝ) (x : E) :
    (planeRotation θ).forward 1 x = SO2FrameGauge.rotate θ x := by
  rw [planeRotation_forward, planeRotationAngle_one]

/--
@isnad1 id=eq.0h3v.s6.7fa99c833861 from=translated src=- shape=89008888 vocab=2c8720a6
-/
@[simp] theorem planeRotation_inverse_endpoint (θ : ℝ) (x : E) :
    (planeRotation θ).inverse 1 x = SO2FrameGauge.rotate (-θ) x := by
  rw [planeRotation_inverse, planeRotationAngle_one]

end SmoothAmbientIsotopy
end Submission
