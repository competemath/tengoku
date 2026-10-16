import Tengoku.NavierStokesEuler.Euler.PacketPhysicalStage
import Tengoku.NavierStokesEuler.Euler.PacketControlledPropagator
import Tengoku.NavierStokesEuler.Euler.PacketTangentNorm

/-!
The arbitrary physical tangent propagator has polynomial loss relative to
the actual primary scalar profile.  All scaled coefficients and tangency
properties are derived from the physical ODEs and parent decomposition.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketStage EulerPacketPerturbation InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
