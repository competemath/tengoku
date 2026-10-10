import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.CompleteContinuity

namespace OAI

universe uM uE

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.LocalizedLinearization
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {E : Type uE} [MetricSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]

def setCutoff (K : Set M) (r : ℝ≥0) (x : M) : ℝ :=
  cutoff (0 : ℝ) r (Metric.infDist x K)

variable [Zero M]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
