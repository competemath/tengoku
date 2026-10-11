import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.TailCoefficients

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
namespace FiniteHead
lemma ancestor_of_boundary_prefix (T : FiniteHead) (v : Vertex) (e : T.Boundary)
    (he : e.val.val <+: v) : T.ancestor v = e.val.val.dropLast := by
  have hv : v ∉ T.vertices := fun hv => T.no_boundary_prefix_head hv e he
  rw [T.ancestor_of_not_mem hv, T.exit_eq v hv e he]

section CoefficientJoint
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ]
  [hιdecidable : DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] (h₂ : MemLp (fun w : ℝ => w) 2 μ)

lemma stitched_head_polynomial {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (T : FiniteHead) (e : ι → T.Boundary) (a : T.vertices → ℝ)
    (z : ((ι → Sample) × Sample) × Sample) :
    (∑ v : T.vertices, a v * pathProduct v (T.stitched e z)) =
      ∑ v : T.vertices, a v * pathProduct v z.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  rw [T.stitched_head e z v v.property]

end CoefficientJoint
end FiniteHead
end IndependentProducts

end

end OAI
