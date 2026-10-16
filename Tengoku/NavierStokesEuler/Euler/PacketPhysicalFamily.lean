import Tengoku.NavierStokesEuler.Euler.PacketPhysicalNeighbor
import Tengoku.NavierStokesEuler.Euler.PacketBeforeTargetSize
import Tengoku.NavierStokesEuler.Euler.PacketScalarUniqueness

/-!
Uniform neighboring amplification and before-target size control from the
actual physical equations.  The scalar reference is shared by uniqueness,
so its choice is independent of the physical label.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
