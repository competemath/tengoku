import Tengoku.NavierStokesEuler.Euler.PacketProfileRecursion
import Tengoku.NavierStokesEuler.Euler.FiniteGradeAssembly

/-! The constructed recursive forcing equals the full nonlinear coefficient forcing. -/

noncomputable section

namespace EulerPacketProfileRecursion

open EulerSmoothLimit EulerPacketPointJets EulerFiniteGrades InnerProductSpace

@[simp] theorem zero_high : (0 : Profile).high=0 := rfl
@[simp] theorem zero_mean : (0 : Profile).mean=0 := rfl
@[simp] theorem zero_corrector : (0 : Profile).corrector=0 := rfl
@[simp] theorem zero_highPressure : (0 : Profile).highPressure=0 := rfl
@[simp] theorem zero_meanPressure : (0 : Profile).meanPressure=0 := rfl

theorem slicedJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set ℝ) (z : Domain) : slicedJet s (0 : Domain → E) z=0 := by
  simp [slicedJet, joinDerivative]

def assembledJets (O : Operators) (N : ℕ) (a : ℕ → Profile) (z : Domain) : ℕ → VectorJet :=
  assemble N (fun i => slicedJet O.interval (a i).high z+slicedJet O.interval (a i).mean z)
    (fun i => slicedJet O.interval (a i).corrector z)

theorem assembledJets_eq_velocityJet (O : Operators) (N : ℕ) (a : ℕ → Profile)
    (ha : a 0=0) (z : Domain) (i : ℕ) (hi : i ≤ N) :
    assembledJets O N a z i=velocityJet O.interval a z i := by
  by_cases hz : i=0
  · subst i
    unfold assembledJets
    rw [assemble_zero N _ _ (by rw [ha]; simp [slicedJet_zero])]
    simp [velocityJet]
  · unfold assembledJets
    rw [assemble_interior N i (by omega) hi]
    simp only [velocityJet, hz, ite_false]

theorem velocityJet_primary (O : Operators) (a : ℕ → Profile) (ha : a 0=0)
    (hmean : (a 1).mean=0) (z : Domain) :
    velocityJet O.interval a z 1=slicedJet O.interval (a 1).high z := by
  simp only [velocityJet, one_ne_zero, ite_false, hmean, Nat.sub_self, ha]
  simp [slicedJet_zero]

def fullForce (O : Operators) (N p : ℕ) (a : ℕ → Profile) : VectorField :=
  fun z => -(linearPart (O.strain z) (slicedJet O.interval (a (p-1)).corrector z)+
    slowPressure (O.inverseFrame z) (pressureJet (a (p-1)).highPressure z)+
    nonlinearGrade (N+1) p (O.inverseFrame z) (O.normal z) (assembledJets O N a z))

end EulerPacketProfileRecursion
