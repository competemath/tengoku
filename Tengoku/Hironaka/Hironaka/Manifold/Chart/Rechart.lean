/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Seed.Geometry.Manifold.Diffeomorph

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Re-charting a manifold by charts of its maximal atlas

Mathlib's `ChartedSpace` fixes one preferred chart `chartAt H x` at every point, and statements
such as "in the chart at `p`, the function is a monomial in the coordinates" refer to it. A
manifold `M` admits many charted-space structures with the same maximal atlas; this module picks
one with prescribed charts and moves it to a homeomorphic copy of `M` (for instance a
`ULift`, to change universes).

Given a homeomorphism `e : M' ≃ₜ M` and, for every point `x : M`, a chart `c x` of the maximal
atlas of `M` whose source contains `x`, `rechartedSpace e c hc` is the charted-space structure on
`M'` whose chart at `p` is `e` followed by `c (e p)`. Its transition maps are those of the charts
`c x` of `M`, so it is a manifold (`isManifold_rechartedSpace`) for which `e` is a diffeomorphism
(`rechartedDiffeomorph`): in the charts `e ≫ c x` of `M'` and `c x` of `M`, the map `e` reads as
the identity. The extended chart of `M'` at `p` is `c (e p) ∘ e` followed by the model embedding
(`extChartAt_rechartedSpace`).
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] {M' : Type*} [TopologicalSpace M']

/-- **The charted space on `M'` with the charts `e ≫ c (e p)`**: for a homeomorphism `e : M' ≃ₜ M`
and charts `c x` of `M` with `x ∈ (c x).source`, the atlas `{e ≫ c x}` with the chart at `p` equal
to `e ≫ c (e p)`.-/
@[instance_reducible]
def rechartedSpace (e : M' ≃ₜ M) (c : M → OpenPartialHomeomorph M H)
    (hc : ∀ x, x ∈ (c x).source) : ChartedSpace H M' where
  atlas := range fun x => e.toOpenPartialHomeomorph.trans (c x)
  chartAt p := e.toOpenPartialHomeomorph.trans (c (e p))
  mem_chart_source p := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    exact ⟨mem_univ _, hc (e p)⟩
  chart_mem_atlas p := ⟨e p, rfl⟩

/-- The chart of `rechartedSpace e c hc` at `p` is `e ≫ c (e p)`.
@isnad1 id=eq.1h6v.s6.e7a6ac834aa1 from=translated src=- shape=8fea3dce vocab=49b009d4
-/
theorem chartAt_rechartedSpace (e : M' ≃ₜ M) (c : M → OpenPartialHomeomorph M H)
    (hc : ∀ x, x ∈ (c x).source) (p : M') :
    @chartAt H _ M' _ (rechartedSpace e c hc) p =
      e.toOpenPartialHomeomorph.trans (c (e p)) :=
  rfl

/-- The extended chart of the re-charted space at `p` is `I ∘ c (e p) ∘ e`.
@isnad1 id=eq.1h10v.s7.4e2aeeb97b94 from=translated src=- shape=cf723a73 vocab=3a7b2431
-/
theorem extChartAt_rechartedSpace (e : M' ≃ₜ M) (c : M → OpenPartialHomeomorph M H)
    (hc : ∀ x, x ∈ (c x).source) (p q : M') :
    letI := rechartedSpace e c hc
    extChartAt I p q = I (c (e p) (e q)) :=
  rfl

/-- The transition map between two charts `e ≫ c x` and `e ≫ c y` is that between `c x` and
`c y`: the homeomorphism `e` cancels.
@isnad1 id=eq.0h7v.s6.2be1ec594e32 from=translated src=- shape=10b3ab27 vocab=d98d1ae4
-/
theorem trans_symm_trans_trans_toOpenPartialHomeomorph (e : M' ≃ₜ M)
    (c : M → OpenPartialHomeomorph M H) (x y : M) :
    (e.toOpenPartialHomeomorph.trans (c x)).symm.trans (e.toOpenPartialHomeomorph.trans (c y)) =
      (c x).symm.trans (c y) := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_trans_self, Homeomorph.refl_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.refl_trans]

/-- A map which, read in two charts, agrees with the identity on the target of the extended chart
is smooth at every point of that target.-/
private theorem contDiffWithinAt_of_eqOn_target (φ : OpenPartialHomeomorph M H) {g : E → E}
    {w : M} (hw : w ∈ φ.source) (hg : EqOn g id (φ.extend I).target) :
    ContDiffWithinAt 𝕜 n g (range I) (φ.extend I w) := by
  have hmem : φ.extend I w ∈ (φ.extend I).target :=
    (φ.extend I).map_source (by rwa [OpenPartialHomeomorph.extend_source])
  refine contDiffWithinAt_id.congr_of_eventuallyEq ?_ (hg hmem)
  filter_upwards [φ.extend_target_mem_nhdsWithin (I := I) hw] with v hv
  exact hg hv

variable [ChartedSpace H M]

/-- **The re-charted space is a manifold** when the charts `c x` belong to the maximal atlas of
`M`: its transition maps are the transition maps `(c x)⁻¹ ≫ c y` of `M`
(`trans_symm_trans_trans_toOpenPartialHomeomorph`), which lie in the groupoid.
@isnad1 id=ismanifo.2h9v.s7.a04a955b8ec8 from=translated src=- shape=19413bcf vocab=eef8820d
-/
theorem isManifold_rechartedSpace [IsManifold I n M] (e : M' ≃ₜ M)
    (c : M → OpenPartialHomeomorph M H) (hc : ∀ x, x ∈ (c x).source)
    (hcm : ∀ x, c x ∈ maximalAtlas I n M) :
    @IsManifold 𝕜 _ E _ _ H _ I n M' _ (rechartedSpace e c hc) := by
  let := rechartedSpace e c hc
  refine { compatible := ?_ }
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  dsimp only
  rw [trans_symm_trans_trans_toOpenPartialHomeomorph]
  exact IsManifold.compatible_of_mem_maximalAtlas (hcm x) (hcm y)

variable [IsManifold I n M] (e : M' ≃ₜ M) (c : M → OpenPartialHomeomorph M H)
  (hc : ∀ x, x ∈ (c x).source) (hcm : ∀ x, c x ∈ maximalAtlas I n M)

include hcm in
/-- In the re-charted structure, `e : M' → M` is smooth: read in the charts `e ≫ c x` and `c x`,
it is the identity.
@isnad1 id=contmdif.2h9v.s7.db83c5365827 from=translated src=- shape=e9932093 vocab=4e61dcb1
-/
theorem contMDiff_rechartedSpace :
    letI := rechartedSpace e c hc
    ContMDiff I I n e := by
  let := rechartedSpace e c hc
  have := isManifold_rechartedSpace e c hc hcm
  intro p
  have hmem : e.toOpenPartialHomeomorph.trans (c (e p)) ∈ maximalAtlas I n M' :=
    IsManifold.chart_mem_maximalAtlas p
  have hsrc : p ∈ (e.toOpenPartialHomeomorph.trans (c (e p))).source :=
    mem_chart_source H p
  rw [contMDiffAt_iff_of_mem_maximalAtlas hmem (hcm (e p)) hsrc (hc (e p))]
  refine ⟨e.continuous.continuousAt, ?_⟩
  have h := contDiffWithinAt_of_eqOn_target (I := I) (n := n) (g := ((c (e p)).extend I ∘ e ∘
    ((e.toOpenPartialHomeomorph.trans (c (e p))).extend I).symm)) (c (e p)) (hc (e p))
    (fun v hv => ?_)
  · simpa [OpenPartialHomeomorph.extend] using h
  rw [OpenPartialHomeomorph.extend_target] at hv
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
    ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
    OpenPartialHomeomorph.coe_trans_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    Function.comp_apply, Homeomorph.apply_symm_apply, id]
  rw [(c (e p)).right_inv hv.1, I.right_inv hv.2]

include hcm in
/-- In the re-charted structure, `e⁻¹ : M → M'` is smooth: read in the charts `c x` and
`e ≫ c x`, it is the identity.
@isnad1 id=contmdif.2h9v.s7.6f1a1d5ec154 from=translated src=- shape=782bb6bc vocab=76a7cd61
-/
theorem contMDiff_symm_rechartedSpace :
    letI := rechartedSpace e c hc
    ContMDiff I I n e.symm := by
  let := rechartedSpace e c hc
  have := isManifold_rechartedSpace e c hc hcm
  intro x
  have hmem : e.toOpenPartialHomeomorph.trans (c x) ∈ maximalAtlas I n M' :=
    IsManifold.subset_maximalAtlas ⟨x, rfl⟩
  have hsrc : e.symm x ∈ (e.toOpenPartialHomeomorph.trans (c x)).source := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    exact ⟨mem_univ _, by simpa using hc x⟩
  rw [contMDiffAt_iff_of_mem_maximalAtlas (hcm x) hmem (hc x) hsrc]
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have h := contDiffWithinAt_of_eqOn_target (I := I) (n := n)
    (g := ((e.toOpenPartialHomeomorph.trans (c x)).extend I ∘ e.symm ∘ ((c x).extend I).symm))
    (c x) (hc x) (fun v hv => ?_)
  · exact h
  rw [OpenPartialHomeomorph.extend_target] at hv
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
    ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
    OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
    Function.comp_apply, Homeomorph.apply_symm_apply, id]
  rw [(c x).right_inv hv.1, I.right_inv hv.2]

/-- **`e` as a diffeomorphism** from `M'` with the re-charted structure to `M`.-/
def rechartedDiffeomorph :
    letI := rechartedSpace e c hc
    Diffeomorph I I M' M n :=
  letI := rechartedSpace e c hc
  { e.toEquiv with
    contMDiff_toFun := contMDiff_rechartedSpace e c hc hcm
    contMDiff_invFun := contMDiff_symm_rechartedSpace e c hc hcm }

/-- The diffeomorphism `rechartedDiffeomorph` is `e` on points.
@isnad1 id=eq.2h9v.s8.756296fc6475 from=translated src=- shape=c6ff14fc vocab=c44d2533
-/
theorem coe_rechartedDiffeomorph : ⇑(rechartedDiffeomorph e c hc hcm) = e :=
  rfl

end Manifold
