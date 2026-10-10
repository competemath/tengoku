import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.CompactSupports

namespace OAI

universe uM

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

structure LocalizationState (R : ℝ≥0) where
  seq : ℕ → Space M
  weak : WeakSequences.WeakNull seq
  set : Set M
  closed : IsClosed set
  zero_mem : (0 : M) ∈ set
  bounded : set ⊆ Metric.closedBall 0 (R : ℝ)
  support : ∀ i, seq i ∈ supported set

end LipschitzCounterexample.FreeSpace

end

end OAI
