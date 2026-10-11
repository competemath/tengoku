import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.CubeGeometry

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubeTransfer
open MeasureTheory Set Filter
open scoped BigOperators
noncomputable section
variable {m : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => CubePoincare.cube (m := m)

end
end UniformSparsestCut.CubeTransfer

namespace UniformSparsestCut.ContractionAverage
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u2} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "μ" => CubePoincare.cube (m := m+1)
open ContractionCore

end
end UniformSparsestCut.ContractionAverage

end

end OAI
