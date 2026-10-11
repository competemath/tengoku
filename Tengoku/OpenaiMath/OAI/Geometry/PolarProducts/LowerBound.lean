import Tengoku.OpenaiMath.OAI.Geometry.PolarProducts.PolarApproximation

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem gromovWidth_mono {U V : Set (Phase n)} (h : U ⊆ V) :
    gromovWidth U ≤ gromovWidth V := by
  apply sSup_le_sSup
  rintro _ ⟨c, ⟨hc, he⟩, rfl⟩
  exact ⟨c, ⟨hc, he.mono_target h⟩, rfl⟩

end
end SymmetricPolar
end LowerBoundInline

end OAI
