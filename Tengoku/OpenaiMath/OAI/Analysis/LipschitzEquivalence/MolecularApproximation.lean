import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.SmoothHilbert

namespace OAI

universe uM

noncomputable section
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology BigOperators
open Filter Set Metric LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def molecule (p q : M) : Space M := (dist p q)⁻¹ • (point p-point q)

@[simp] theorem molecule_self (p : M) : molecule p p = 0 := by simp [molecule]

structure MolecularData (M : Type uM) where
  n : ℕ
  coeff : Fin n → ℝ
  p : Fin n → M
  q : Fin n → M

namespace MolecularData

def vector (a : MolecularData M) : Space M := ∑ i, a.coeff i • (point (a.p i)-point (a.q i))
def cost (a : MolecularData M) : ℝ := ∑ i, |a.coeff i| * dist (a.p i) (a.q i)

end MolecularData

end LipschitzCounterexample.FreeSpace
end

end OAI
