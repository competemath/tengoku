import Tengoku.NavierStokesEuler.Euler.PacketFrameCoefficients
import Tengoku.NavierStokesEuler.Euler.PacketCoefficientMotion
import Tengoku.NavierStokesEuler.Euler.PacketScaledRay

/-!
Physical operator bounds and the actual homogeneous primary imply the
small scaled matrix errors used in source propagation.  The fixed numerical
loss absorbs rotation of the normalized frame.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketCoefficientControl InnerProductSpace ContinuousLinearMap

def rescaledFrame (B : ℝ → Space →L[ℝ] Space) (m v : ℝ → Space)
    (t₀ a ε τ : ℝ) : Fin 3 → Fin 3 → ℝ :=
  frameMatrix (B (physicalTime t₀ a ε τ))
    (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε τ)))

def rescaledShear (c : ℝ) (m v : ℝ → Space) (t₀ a ε τ : ℝ) : ℝ :=
  primaryShear c m v (physicalTime t₀ a ε τ)

end EulerPacketMovingFrame
