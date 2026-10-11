import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.CubeTransfer

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceContraction
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
noncomputable section
variable {m : ℕ}
local notation "d" => (m+1:ℕ)
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "μ" => (CubePoincare.cube (m:=d))
end
end UniformSparsestCut.SourceContraction

end

end OAI
