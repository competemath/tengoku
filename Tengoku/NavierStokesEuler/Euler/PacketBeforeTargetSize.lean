import Tengoku.NavierStokesEuler.Euler.PacketSizeComparison

/-!
The before-target part of the physical primary-size estimate.  The input
is the actual ray and velocity error already obtained from the physical
equations, and the comparison function solves the scalar reference ODE.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketGrowth EulerPacketFrameStability InnerProductSpace

end EulerPacketMovingFrame
