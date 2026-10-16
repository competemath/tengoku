import Tengoku.NavierStokesEuler.Euler.PacketScaledVelocity

/-! The physical activation data give the scaled initial conditions. -/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketRay InnerProductSpace

/-- The signed physical `p` component in (26) becomes a nonnegative
scalar initial slope, with the expected factor `ε⁻¹`. -/
theorem activation_scaled_velocity {m v w : ℝ → Space} {t₀ a ε C γ : ℝ}
    (hε : 0 < ε) (hγlo : -C ≤ γ) (hγhi : γ ≤ 0)
    (hp : ⟪unit (m t₀),w t₀⟫_ℝ = γ) (hq : ⟪unit (v t₀),w t₀⟫_ℝ = 1) :
    0 ≤ -γ/ε ∧ -γ/ε ≤ C/ε ∧
      scaledVelocity m v w t₀ a ε 0 0 = -(-γ/ε) ∧
      scaledVelocity m v w t₀ a ε 0 1 = 1 := by
  have hu : scaledVelocity m v w t₀ a ε 0 0 = γ/ε := by
    norm_num [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
      velocityScale, Fin.ext_iff, hp]
  have hv : scaledVelocity m v w t₀ a ε 0 1 = 1 := by
    norm_num [scaledVelocity, movingVelocity, physicalTime, normalizedFrame, frame,
      velocityScale, Fin.ext_iff, hq]
  refine ⟨div_nonneg (neg_nonneg.mpr hγhi) hε.le,
    div_le_div_of_nonneg_right (by linarith only [hγlo]) hε.le, ?_, hv⟩
  rw [hu]
  ring

theorem activation_tangent_pairing {m v r w : ℝ → Space} {s₀ t₀ : ℝ}
    (hr : r t₀ = s₀ • cross (unit (m t₀)) (unit (v t₀)))
    (hw : ⟪cross (unit (m t₀)) (unit (v t₀)),w t₀⟫_ℝ = 0) :
    ⟪r t₀,w t₀⟫_ℝ = 0 := by
  rw [hr, real_inner_smul_left, hw, mul_zero]

end EulerPacketMovingFrame
