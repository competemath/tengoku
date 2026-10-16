import Tengoku.NavierStokesEuler.Euler.PacketPhysicalCoefficients

/-! Actual shear motion, exposed for the compression scale guard. -/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketCoefficientControl InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
