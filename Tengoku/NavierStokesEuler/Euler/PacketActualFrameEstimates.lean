import Tengoku.NavierStokesEuler.Euler.PacketPhysicalFrameRenewal
import Tengoku.NavierStokesEuler.Euler.PacketScaledVelocitySystem

/-!
The quantified source frame-renewal bounds concern the actual normalized
physical vectors.  The third ratio is eliminated using actual tangency,
and the scalar estimate is transported through the checked exact formulas.
-/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketRay EulerPacketFrameStability
  EulerPacketFrameQuantitative InnerProductSpace

theorem thirdRatio_from_pairing (R V : Fin 3 → ℝ) (hN : R 2 ≠ 0) (hV : V 1 ≠ 0)
    (hpair : R 0*V 0+R 1*V 1+R 2*V 2 = 0) :
    V 2/V 1 = velocityThird (R 0) (R 1) (R 2) (V 0/V 1) 1 := by
  unfold velocityThird
  apply (eq_div_iff hN).mpr
  field_simp
  linarith only [hpair]

end EulerPacketMovingFrame
