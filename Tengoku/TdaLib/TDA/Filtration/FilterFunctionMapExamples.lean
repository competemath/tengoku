import Tengoku.TdaLib.TDA.Filtration.FilterFunctionMap
import Tengoku.TdaLib.TDA.Filtration.CechExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Filter reparametrization fixtures

The fixtures test the `FilterFunction.map` and `FilterFunction.scale` definitions on
the merged two-point Rips filter: the scaled sublevels at `2` and `4` are the original
sublevels at `1` and `2`, so the edge appears exactly at the scaled threshold `4`. Negating
the same filter violates monotonicity, so order reversal is not a reparametrization. Scaling
by `2` and then by `2⁻¹` returns every real filter.
-/

namespace TDA.Filtration.FilterFunctionMapExamples

open TDA.Simplicial Cech.Examples

/-- The merged diameter filter of the two labelled points `0` and `2` on the line.-/
noncomputable abbrev f : FilterFunction (Rips.fullComplex (Fin 2)) ℝ :=
  Rips.filter TwoPoints.metric

/-! ### Threshold naturality -/

/--
@isnad1 id=eq.0h0v.s6.b63b7d68f9b0 from=translated src=- shape=1ecfda2b vocab=44ced506
-/
theorem scale_sublevel_two : (f.scale 2 two_pos).sublevel 2 = f.sublevel 1 := by
  rw [FilterFunction.scale_sublevel]
  norm_num

/--
@isnad1 id=eq.0h0v.s6.046e0212bb8a from=translated src=- shape=1ecfda2b vocab=44ced506
-/
theorem scale_sublevel_four : (f.scale 2 two_pos).sublevel 4 = f.sublevel 2 := by
  rw [FilterFunction.scale_sublevel]
  norm_num

/-- The edge is absent from the scaled sublevel at `2`.
@isnad1 id=not.0h0v.s6.b21b14c6651b from=translated src=- shape=22c73545 vocab=db2d21b7
-/
theorem edge_not_mem_scale_two : TwoPoints.edge ∉ (f.scale 2 two_pos).sublevel 2 := by
  rw [scale_sublevel_two]
  exact TwoPoints.edge_not_mem_rips_one

/-- The edge is present in the scaled sublevel at `4`.
@isnad1 id=mem.0h0v.s6.ae206f5a2793 from=translated src=- shape=8077c6d4 vocab=db2d21b7
-/
theorem edge_mem_scale_four : TwoPoints.edge ∈ (f.scale 2 two_pos).sublevel 4 := by
  rw [scale_sublevel_four]
  exact TwoPoints.edge_mem_rips_two

/-- The scaled edge value is `2 * 2 = 4`.
@isnad1 id=eq.0h0v.s5.e1a7a5798a26 from=translated src=- shape=f235e112 vocab=4d359eb0
-/
theorem scale_edge_value : (f.scale 2 two_pos).value TwoPoints.edgeFace = 4 := by
  rw [FilterFunction.scale_value, TwoPoints.rips_value]
  norm_num

/-! ### Order reversal is not a reparametrization -/

/-- The vertex `{0}` as a face.-/
def vertexFace : TotalFace (Rips.fullComplex (Fin 2)) := ⟨{0}, Finset.singleton_nonempty 0⟩

/--
@isnad1 id=eq.0h0v.s4.350c04a15563 from=translated src=- shape=1cf84b2f vocab=951186be
-/
theorem vertex_value : f.value vertexFace = 0 := by
  rw [Rips.filter_value]
  exact Rips.diameter_singleton _ _

/-- No filter has the negated values of the two-point Rips filter: monotonicity along
`{0} ⊆ {0, 1}` would give `0 ≤ -2`.
@isnad1 id=not.0h0v.s6.4dd462c783cc from=translated src=- shape=99f4b0d1 vocab=aca074e5
-/
theorem no_negated_filter :
    ¬ ∃ g : FilterFunction (Rips.fullComplex (Fin 2)) ℝ, ∀ s, g.value s = -(f.value s) := by
  rintro ⟨g, hg⟩
  have hsub : vertexFace.val ⊆ TwoPoints.edgeFace.val := by
    simp [vertexFace, TwoPoints.edgeFace, TwoPoints.edge]
  have h := g.mono hsub
  rw [hg, hg, vertex_value, TwoPoints.rips_value] at h
  norm_num at h

/-! ### Round trip -/

/-- Scaling by `2` and then by `2⁻¹` returns the filter.
@isnad1 id=eq.0h3v.s5.a350ae59d9d0 from=translated src=- shape=bcd95ab7 vocab=66e684cd
-/
theorem scale_round_trip {V : Type*} {K : PreAbstractSimplicialComplex V}
    (g : FilterFunction K ℝ) :
    (g.scale 2 two_pos).scale 2⁻¹ (inv_pos.2 two_pos) = g := by
  rw [FilterFunction.scale_scale]
  convert FilterFunction.scale_one g using 2
  norm_num

end TDA.Filtration.FilterFunctionMapExamples
