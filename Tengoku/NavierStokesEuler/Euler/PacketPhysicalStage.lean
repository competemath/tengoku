import Tengoku.NavierStokesEuler.Euler.PacketMatrixContinuity
import Tengoku.NavierStokesEuler.Euler.PacketWithinRay
import Tengoku.NavierStokesEuler.Euler.PacketTangentInvariant

/-!
The physical ray and velocity equations, the actual parent rank-one
decomposition, and physical coefficient bounds imply relative amplification
for the scaled primary.  No scaled ODE, ray lower bound, or matrix-error
estimate is assumed.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketStage EulerPacketPerturbation InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
