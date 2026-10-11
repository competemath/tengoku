import Tengoku.NavierStokesEuler.Euler.PacketRecursiveCancellation

/-! The initial profile and the zero/first grades of the actual recursive packet. -/

noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades EulerPacketResidual InnerProductSpace Finset

def primaryProfile (O : Operators) (A : VectorField) (π : ScalarField) : Profile :=
  ⟨A,0,O.curlCorrector A,π,0⟩

theorem assembledJets_zero (O : Operators) (N : ℕ) (a : ℕ → Profile) (ha : a 0=0) (z : Domain) :
    assembledJets O N a z 0=0 := by
  unfold assembledJets
  apply assemble_zero
  rw [ha]
  simp [EulerPacketPointJets.slicedJet_zero']

theorem pressureJets_zero (N : ℕ) (a : ℕ → Profile) (ha : a 0=0) (z : Domain) :
    pressureJets N a z 0=0 := by
  unfold pressureJets
  apply assemble_zero
  rw [ha]
  simp [pressureJet_zero]

end EulerPacketProfileRecursion
