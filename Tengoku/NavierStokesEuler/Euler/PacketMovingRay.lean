import Tengoku.NavierStokesEuler.Euler.PacketMovingFrame

/-! The physical ray ODE in the actual normalized moving frame. -/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary InnerProductSpace ContinuousLinearMap

def movingRay (m v r : ℝ → Space) (t : ℝ) (i : Fin 3) : ℝ :=
  ⟪normalizedFrame m v t i,r t⟫_ℝ

end EulerPacketMovingFrame
