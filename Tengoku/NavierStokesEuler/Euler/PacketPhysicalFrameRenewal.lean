import Tengoku.NavierStokesEuler.Euler.PacketPhysicalSize
import Tengoku.NavierStokesEuler.Euler.PacketOrientedCoordinates
import Tengoku.NavierStokesEuler.Euler.PacketFrameRenewalAlgebra

/-!
The source's next-frame scalar formulas represent the actual normalized
physical ray and velocity.  Orientation, physical norms, and pressure
numerators are identified exactly before any quantitative estimate is used.
-/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketRay EulerPacketFrameStability InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
