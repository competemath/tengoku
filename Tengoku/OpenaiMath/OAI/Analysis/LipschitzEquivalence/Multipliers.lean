import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.SupportedDuality

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

def multiplier (φ : M → ℝ) : Space M →L[ℝ] Space M :=
  linearize (fun x => φ x • point x)

end LipschitzCounterexample.FreeSpace
namespace LipschitzCounterexample.FreeSpace
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

def Approximable (μ : Space M) (K : Set M) (ε : ℝ) : Prop :=
  ∃ ν : Space M, ν ∈ supported K ∧ ‖μ-ν‖ < ε

end LipschitzCounterexample.FreeSpace

end

end OAI
