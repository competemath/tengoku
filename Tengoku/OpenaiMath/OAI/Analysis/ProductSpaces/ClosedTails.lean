import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.Resampling

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
section Tails
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end Tails
end IndependentProducts

end

end OAI
