import Tengoku.NavierStokesEuler.Euler.PacketGeometryData
import Tengoku.NavierStokesEuler.Euler.PacketShearMotion

/-! Consequences of the literal numerical guards for a physical geometry stage. -/

noncomputable section

namespace EulerPacketMovingFrame.PhysicalGeometryData

open Set Real EulerSmoothLimit EulerPacketRay EulerPacketFrameQuantitative

variable {α : Type*} (D : PhysicalGeometryData α)

theorem a_pos : 0 < D.a := by linarith only [D.a_lower]
theorem Theta_pos : 0 < D.Θ := by linarith only [D.Theta_lower]
theorem error_nonneg : 0 ≤ D.error := by unfold error; positivity [D.epsilon_pos, D.Theta_pos, D.d_nonneg]

theorem target_from_sigma : 1/D.σ ≤ D.target := by
  have hy : 1 ≤ D.y⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ D.y_pos).mpr
    linarith only [D.y_small]
  exact div_le_div_of_nonneg_right hy D.sigma_pos.le

theorem target_one : 1 ≤ D.target := by
  have hs : 1 ≤ 1/D.σ := (le_div_iff₀ D.sigma_pos).mpr (by linarith only [D.sigma_small])
  exact hs.trans D.target_from_sigma

theorem target_pos : 0 < D.target := lt_of_lt_of_le zero_lt_one D.target_one
theorem horizon_one : 1 ≤ D.H := D.target_one.trans D.target_le_horizon
theorem horizon_pos : 0 < D.H := lt_of_lt_of_le zero_lt_one D.horizon_one
theorem target_le_Theta : D.target ≤ D.Θ := D.target_le_horizon.trans D.horizon_le_Theta

theorem sigma_Theta : 1 ≤ D.σ*D.Θ := by
  have h := (div_le_iff₀ D.sigma_pos).mp (D.target_from_sigma.trans D.target_le_Theta)
  nlinarith only [h]

theorem target_scale : 1 ≤ D.σ^2*D.target^2 := by
  have h : 1 ≤ D.σ*D.target := by
    have hh := (div_le_iff₀ D.sigma_pos).mp D.target_from_sigma
    nlinarith only [hh]
  have hh := mul_le_mul h h (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ D.σ*D.target)
  nlinarith only [hh]

theorem time_mem {τ : ℝ} (hτ : τ ∈ Icc 0 D.H) : D.time τ ∈ D.S :=
  D.time_maps ⟨hτ.1, hτ.2.trans D.horizon_le_Theta⟩

theorem target_time_mem : D.targetTime ∈ D.S :=
  D.time_mem ⟨D.target_pos.le, D.target_le_horizon⟩

theorem error_le_half : D.error ≤ 1/2 := by
  have hp := scaled_power_le D.Theta_lower
    ((by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge) D.error_nonneg
    (by decide : 0 ≤ 40)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  norm_num only [pow_zero, mul_one] at hp
  nlinarith only [hp, hs]

theorem error_le_one : D.error ≤ 1 := D.error_le_half.trans (by norm_num)

theorem epsilon_le_error : D.ε ≤ D.error := by
  have hg : 1 ≤ (4*D.G)^2 := by nlinarith only [D.G_lower, sq_nonneg (D.G-1)]
  have hc : 1 ≤ D.Θ*(4*D.G)^2 := by
    simpa only [one_mul] using mul_le_mul D.Theta_lower hg
      (by norm_num : (0:ℝ) ≤ 1) D.Theta_pos.le
  have hh := mul_le_mul_of_nonneg_left hc D.epsilon_pos.le
  unfold error
  nlinarith only [hh, D.d_nonneg, D.epsilon_pos]

theorem epsilon_le_one : D.ε ≤ 1 := D.epsilon_le_error.trans D.error_le_one

theorem ray_error_small : 800*D.error*D.Θ^5 ≤ 1/2 := by
  have hp := scaled_power_le D.Theta_lower
    ((by norm_num : (1:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge) D.error_nonneg
    (by decide : 5 ≤ 40)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  nlinarith only [hp, hs]

theorem relative_error_small : neighborStabilityConstant*D.error*D.Θ^29 ≤ 1/2 := by
  have hK : 0 ≤ neighborStabilityConstant := (by norm_num : (0:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 29 ≤ 40))
    (mul_nonneg hK D.error_nonneg)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  nlinarith only [hp, hs]

theorem scalar_error_small : 4*exp 6*(400000000*D.error*D.Θ^29) ≤ 1 := by
  have hr := D.relative_error_small
  have hK : 0 ≤ neighborStabilityConstant :=
    (by norm_num : (0:ℝ) ≤ 1000000000).trans neighborStabilityConstant_ge
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 29 ≤ 40))
    (mul_nonneg hK D.error_nonneg)
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  unfold neighborStabilityConstant at hp hs hr
  nlinarith only [hp, hs, hr]

theorem propagator_small : 8000000*D.error*D.Θ^21 ≤ 1 := by
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ D.Theta_lower (by decide : 21 ≤ 40)) D.error_nonneg
  have hk : 0 ≤ neighborStabilityConstant-8 := by linarith only [neighborStabilityConstant_ge]
  have hmul := mul_nonneg hk (mul_nonneg D.error_nonneg (pow_nonneg D.Theta_pos.le 40))
  have hs := D.small
  change 1000000*neighborStabilityConstant*D.error*D.Θ^40 ≤ 1 at hs
  nlinarith only [hp, hmul, hs]

end EulerPacketMovingFrame.PhysicalGeometryData
