import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.MetricNorm

namespace OAI

universe u_259

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n m : ℕ} [Nonempty (Fin n)]

end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
