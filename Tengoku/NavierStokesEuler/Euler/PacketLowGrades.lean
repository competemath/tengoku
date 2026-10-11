import Tengoku.NavierStokesEuler.Euler.PacketMomentumExpansion

/-! The low coefficients of the actual packet residual, before solving their equations. -/

noncomputable section

namespace EulerPacketResidual

open Finset EulerFiniteGrades

variable {V Q W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup W] [Module ℝ W]

end EulerPacketResidual

namespace EulerPacketPointJets

open Finset EulerSmoothLimit EulerPacketResidual

end EulerPacketPointJets
