import Tengoku.NavierStokesEuler.Euler.PacketGeometryGuards
import Tengoku.NavierStokesEuler.Euler.PacketPhysicalSign
import Tengoku.NavierStokesEuler.Euler.PacketPhysicalCompression
import Tengoku.NavierStokesEuler.Euler.PacketEarlyPhysical
import Tengoku.NavierStokesEuler.Euler.PacketPhysicalPropagator
import Tengoku.NavierStokesEuler.Euler.PacketPropagationTime

/-!
One geometric stage: actual neighboring physical fields, the constructed
common scalar reference, and the source amplitude choice.  All hypotheses
are the literal physical data and explicit scale guards in the data record.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set Real EulerSmoothLimit EulerPacketRay InnerProductSpace PhysicalGeometryData

structure PhysicalGeometryConclusion {α : Type*} (D : PhysicalGeometryData α)
    (F F₁ Z Z₁ : ℝ → ℝ) : Prop where
  initial_values : F 0 = 1 ∧ F₁ 0 = 0 ∧ Z 0 = 1 ∧ Z₁ 0 = D.lam
  F_derivative : ∀ t, HasDerivAt F (F₁ t) t
  Z_derivative : ∀ t, HasDerivAt Z (Z₁ t) t
  F_flux : ∀ t, HasDerivAt (fun s => (1+(D.σ^2*s^2)^2)*F₁ s)
    (2*(1-D.σ^2*(D.σ^2*t^2))*F t) t
  Z_flux : ∀ t, HasDerivAt (fun s => (1+(D.σ^2*s^2)^2)*Z₁ s)
    (2*(1-D.σ^2*(D.σ^2*t^2))*Z t) t
  ray_control : ∀ ξ τ, τ ∈ Icc 0 D.H →
    norm3 (D.ray ξ τ 0-D.σ^2*τ^2) (D.ray ξ τ 1+2*D.σ^2*τ) (D.ray ξ τ 2-1) ≤
      800*D.error*D.Θ^5 ∧ 1/2 ≤ D.ray ξ τ 2 ∧
      ⟪D.r ξ (D.time τ),D.w ξ (D.time τ)⟫_ℝ = 0
  state_error : ∀ ξ τ, τ ∈ Icc 0 D.H →
    |D.velocity ξ τ 1-Z τ|+|D.velocity ξ τ 0+Z₁ τ| ≤ 400000000*D.error*D.Θ^29*(1+D.lam)*F τ
  relative_error : ∀ ξ τ, τ ∈ Icc 1 D.H →
    0 < D.velocity ξ τ 1 ∧ |D.velocity ξ τ 1/Z τ-1| ≤ neighborStabilityConstant*D.error*D.Θ^29 ∧
      |D.velocity ξ τ 0/D.velocity ξ τ 1+Z₁ τ/Z τ| ≤ 10*(neighborStabilityConstant*D.error*D.Θ^29)
  positive_pressure : ∀ ξ τ, τ ∈ Icc 1 D.H →
    0 < ⟪D.r ξ (D.time τ),(D.M ξ (D.time τ)) (D.w ξ (D.time τ))⟫_ℝ
  target_positive : 0 < D.targetSize
  target_growth : D.s₀*exp (1/(4*D.σ)) ≤ 4*D.Θ*D.targetSize
  horizon_size : ∀ ξ τ, τ ∈ Icc 1 D.H → D.size ξ τ ≤ 64*exp 6*D.targetSize
  early_size : ∀ ξ τ, τ ∈ Icc 0 1 →
    D.size ξ τ/D.targetSize ≤ 8232*exp 9*D.Θ^5*exp (-(1/(4*D.σ)))
  next_frame :
    |D.nextCoupling/D.a-1| ≤ D.y^4+D.σ^2*D.y^2+8*D.σ*D.y^3+30000000*neighborStabilityConstant*D.error*D.Θ^40 ∧
    |(D.y⁻¹)^2*D.nextTilt-1| ≤ 1500*D.σ+30000000*neighborStabilityConstant*D.error*D.Θ^40
  compression_bound : D.nextCompression ≤ -(D.targetShear*D.ε)/(10*D.target)+3*(D.G+D.d)
  compression_negative : D.nextCompression < 0
  amplitude_nonneg : 0 ≤ D.amplitude
  amplitude_normalization : D.amplitude*D.targetSize = D.δ*D.hchild
  amplitude_exponential : D.amplitude ≤ (4*D.Θ*D.δ*D.hchild/D.s₀)*exp (-(1/(4*D.σ)))
  amplitude_profile : ∀ τ ∈ Icc 0 D.H, D.amplitude*Z τ ≤ 8*exp 6*D.δ*D.hchild/D.s₀
  amplitude_profile_sup : sSup ((fun τ => D.amplitude*Z τ) '' Icc 0 D.H) ≤ 8*exp 6*D.δ*D.hchild/D.s₀
  physical_profile_continuous :
    ContinuousOn (physicalProfile Z D.t₀ D.a D.ε) (Icc D.t₀ (D.time D.H))
  physical_profile_positive : ∀ t ∈ Icc D.t₀ (D.time D.H), 0 < physicalProfile Z D.t₀ D.a D.ε t
  tangent_propagator : ∀ ξ (u : ℝ → Space),
    (∀ t ∈ D.S, HasDerivWithinAt u
      (-(D.M ξ t) (u t)+(2*⟪D.r ξ t,(D.M ξ t) (u t)⟫_ℝ/‖D.r ξ t‖^2) • D.r ξ t) D.S t) →
    ⟪D.r ξ D.t₀,u D.t₀⟫_ℝ = 0 →
    ∀ s t, s ∈ Icc D.t₀ (D.time D.H) → t ∈ Icc D.t₀ (D.time D.H) → s ≤ t →
      ‖u t‖ ≤ (560*D.Θ^10/D.ε)*
        (physicalProfile Z D.t₀ D.a D.ε t/physicalProfile Z D.t₀ D.a D.ε s)*‖u s‖

end EulerPacketMovingFrame
