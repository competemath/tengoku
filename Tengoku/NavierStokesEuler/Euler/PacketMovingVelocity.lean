import Tengoku.NavierStokesEuler.Euler.PacketMovingRay

/-! The actual projected primary-velocity ODE in the normalized moving frame. -/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace ContinuousLinearMap

theorem frameSkew_antisymm (B : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    frameSkew B j i = -frameSkew B i j := by
  fin_cases i <;> fin_cases j <;> simp [frameSkew, Fin.ext_iff]

theorem frameMatrix_adjoint (B : Space →L[ℝ] Space) (p q : Space) (i j : Fin 3) :
    frameMatrix B.adjoint p q i j = frameMatrix B p q j i := by
  unfold frameMatrix
  rw [adjoint_inner_right, real_inner_comm (frame p q j) (B (frame p q i))]

def movingVelocity (m v w : ℝ → Space) (t : ℝ) (i : Fin 3) : ℝ :=
  ⟪normalizedFrame m v t i,w t⟫_ℝ

def movingFlux (M : Space →L[ℝ] Space) (m v r w : ℝ → Space) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, movingRay m v r t i *
    (∑ j : Fin 3, frameMatrix M (unit (m t)) (unit (v t)) i j * movingVelocity m v w t j)

def movingDenominator (m v r : ℝ → Space) (t : ℝ) : ℝ :=
  ∑ j : Fin 3, (movingRay m v r t j)^2

end EulerPacketMovingFrame
