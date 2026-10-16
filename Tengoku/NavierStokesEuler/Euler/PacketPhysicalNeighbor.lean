import Tengoku.NavierStokesEuler.Euler.PacketPhysicalStage
import Tengoku.NavierStokesEuler.Euler.PacketNeighborControlled

/-!
Actual neighboring physical primaries satisfy the amplification estimate
with their genuine initial discrepancy.  The source moving frame is the
center frame.  Its neighboring matrix perturbation is part of the actual
parent error; all scaled coefficient and ray bounds are derived here.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketStage EulerPacketPerturbation InnerProductSpace ContinuousLinearMap

end EulerPacketMovingFrame
