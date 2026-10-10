import Tengoku.OpenaiMath.OAI.Analysis.LipschitzEquivalence.RadiusReduction

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

def Near (A : Finset M) (δ : ℝ) : Set M :=
  {x | ∃ a ∈ A, dist x a ≤ δ}

omit [Zero M] in
theorem near_mono {A B : Finset M} (h : A ⊆ B) (δ : ℝ) : Near A δ ⊆ Near B δ := by
  rintro x ⟨a,ha,hxa⟩
  exact ⟨a,h ha,hxa⟩

omit [Zero M] in
theorem subset_near (A : Finset M) {δ : ℝ} (hδ : 0 ≤ δ) : (A : Set M) ⊆ Near A δ := by
  intro x hx
  exact ⟨x,hx,by simpa using hδ⟩

end LipschitzCounterexample.FreeSpace

end

end OAI
