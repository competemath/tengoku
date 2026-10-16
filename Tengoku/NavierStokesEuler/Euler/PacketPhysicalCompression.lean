import Tengoku.NavierStokesEuler.Euler.PacketPhysicalSize
import Tengoku.NavierStokesEuler.Euler.PacketFrameCoefficients

/-! The source target-compression estimate for the actual next ray. -/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay EulerPacketFrameRenewal
  EulerPacketTargetCompression InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
