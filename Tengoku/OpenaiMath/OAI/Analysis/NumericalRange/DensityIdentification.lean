import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.TestingAlgebra

namespace OAI

universe u_251 u_252

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_251} {m : Type u_252} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
