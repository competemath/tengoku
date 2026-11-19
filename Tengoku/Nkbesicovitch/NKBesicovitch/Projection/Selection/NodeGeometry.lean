/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Selection.NodeParameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometry of the selected labels at one corner node

Each outer label belongs to the common scalar's outer reservoir. Each
inner label belongs to the corresponding dual time reservoir. Hence every
labeled child triple remains separated inside the original time set.
The labels may repeat numerical heights; all label occurrences satisfy
the same geometric guarantees.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection.SelectableProjectionScheme

variable {m D L : ℕ} {β : ℝ} (S : SelectableProjectionScheme m β D L)

/--
@isnad1 id=mem.5h12v.s7.a49f0d65fb8b from=translated src=- shape=68a5b7f0 vocab=13959302
-/
theorem cornerNodeParameters_outer_time_mem {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (i : Fin L) :
    S.time p.2.1 i ∈ cornerOuterTimes I a b c δ p.1 := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hO : 0 < volume (cornerOuterTimes I a b c δ p.1) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hp.1
  exact S.time_mem _ (measurableSet_cornerOuterTimes hI a b c δ p.1)
    ((cornerOuterTimes_subset I a b c δ p.1).trans hIunit) hO p.2.1 hp.2.1 i

/--
@isnad1 id=mem.5h13v.s8.a2afefd9cfa6 from=translated src=- shape=7b2bfd6f vocab=276a5cf6
-/
theorem cornerNodeParameters_inner_time_mem {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (i j : Fin L) :
    S.time (p.2.2 i) j ∈ dualTimes I b a (cornerInnerCoefficient a c p.1 (S.time p.2.1 i)) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hu := S.cornerNodeParameters_outer_time_mem hI hIunit hIpos hδ hp i
  have hinner := (cornerOuterTimes_spec hu).2.2.2
  have hT : 0 < volume (dualTimes I b a (cornerInnerCoefficient a c p.1 (S.time p.2.1 i))) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hinner
  exact S.time_mem _ (measurableSet_dualTimes hI _ _ _)
    ((dualTimes_subset I _ _ _).trans hIunit) hT _ (hp.2.2 i) j

/--
@isnad1 id=mem.6h13v.s8.1c6dbf22c0ce from=translated src=- shape=07cdabb2 vocab=28370ae1
-/
theorem cornerNodeParameters_child_triple {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b c δ : ℝ} (hδ : 0 < δ) (hb : b ∈ I)
    {p : ℝ × ((Fin D → ℝ) × (Fin L → Fin D → ℝ))}
    (hp : p ∈ S.cornerNodeParameters I a b c δ) (i j : Fin L) :
    ((b, S.time (p.2.2 i) j),
      dualTime b a (cornerInnerCoefficient a c p.1 (S.time p.2.1 i)) (S.time (p.2.2 i) j)) ∈
        separatedTriples I ((volume I).toReal / 100) :=
  dualTimes_mem_separatedTriples hb
    (S.cornerNodeParameters_inner_time_mem hI hIunit hIpos hδ hp i j)

end NKBesicovitch.Projection.Selection.SelectableProjectionScheme
