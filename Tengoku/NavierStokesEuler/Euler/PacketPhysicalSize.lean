import Tengoku.NavierStokesEuler.Euler.PacketScaledVelocity

/-!
Actual physical norms and normalized next-frame coupling in the scaled
coordinates of source (28).  These are identities for the constructed
coordinate maps, rather than assumptions on a model system.
-/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketCrossProduct InnerProductSpace ContinuousLinearMap

def velocityDenominator (ε r w₃ : ℝ) : ℝ := 1+ε^2*(r^2+w₃^2)

theorem velocityDenominator_pos (ε r w₃ : ℝ) : 0 < velocityDenominator ε r w₃ := by
  unfold velocityDenominator
  positivity

def normalizedCoupling (M : Space →L[ℝ] Space) (r w : Space) : ℝ :=
  ⟪unit r,M (unit w)⟫_ℝ

def normalizedTilt (M : Space →L[ℝ] Space) (r w : Space) : ℝ :=
  ⟪cross (unit r) (unit w),M (unit w)⟫_ℝ/normalizedCoupling M r w

theorem normalizedCoupling_eq (M : Space →L[ℝ] Space) (r w : Space) :
    normalizedCoupling M r w = ⟪r,M w⟫_ℝ/(‖r‖*‖w‖) := by
  simp only [normalizedCoupling, unit, map_smul, real_inner_smul_left,
    real_inner_smul_right, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cross_smul_smul (a b : ℝ) (r w : Space) :
    cross (a • r) (b • w) = (a*b) • cross r w := by
  change crossBilinear (a • r) (b • w) = (a*b) • crossBilinear r w
  simp only [map_smul, smul_apply, smul_smul]
  rw [mul_comm b a]

theorem normalizedTilt_eq (M : Space →L[ℝ] Space) (r w : Space)
    (hr : r ≠ 0) (hw : w ≠ 0) (hflux : ⟪r,M w⟫_ℝ ≠ 0) :
    normalizedTilt M r w = ⟪cross r w,M w⟫_ℝ/(‖w‖*⟪r,M w⟫_ℝ) := by
  rw [normalizedTilt, normalizedCoupling_eq]
  simp only [unit, cross_smul_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
  have hrn := norm_ne_zero_iff.mpr hr
  have hwn := norm_ne_zero_iff.mpr hw
  field_simp

end EulerPacketMovingFrame
