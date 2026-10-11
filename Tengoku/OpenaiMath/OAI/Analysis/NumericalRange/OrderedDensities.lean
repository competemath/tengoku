import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.PositiveDensity

namespace OAI

universe u_255 u_256

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_255} {m : Type u_256} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
