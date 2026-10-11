import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.UniformReplication
import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.VertexCount

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceUniform
open scoped BigOperators
open SourceMetric SourceParameters
noncomputable section
lemma size_upper {d v : ℕ} (hd : 3≤d) (hv : v≤d^(4025*d)) :
    d^d+d^2*v+v≤d^(4030*d) := by
  have hd1 : 1≤d := by omega
  have hp : d^d≤d^(4025*d+2) := Nat.pow_le_pow_right hd1 (by omega)
  have hv' : v≤d^(4025*d+2) := hv.trans (Nat.pow_le_pow_right hd1 (by omega))
  have hprod : d^2*v≤d^(4025*d+2) := by
    calc
      _ ≤ d^2*d^(4025*d) := Nat.mul_le_mul_left _ hv
      _ = _ := by rw [←pow_add]; congr 1; omega
  calc
    _ ≤ 3*d^(4025*d+2) := by omega
    _ ≤ d*d^(4025*d+2) := Nat.mul_le_mul_right _ hd
    _ = d^(4025*d+3) := by rw [←pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right hd1 (by omega)

end
end UniformSparsestCut.SourceUniform

end

end OAI
