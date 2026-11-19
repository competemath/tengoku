/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Selection.DualScalarBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The measurable relation between times and dual scalars

A pair `(t,c)` is admissible when `c` is nonzero and `t` and its dual
time belong to the separated pair domain. This relation is jointly Borel
in measurable families of time sets and base heights. Its scalar sections
are images under the rational change of variables, and their measures
admit a uniform Jacobian lower bound.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Admissible pairs of a time and a nonzero dual-code scalar.-/
noncomputable def dualTimeRelation (I : Set ℝ) (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ≠ 0 ∧ (p.1, dualTime a b p.2 p.1) ∈ dualPairParameters I a b}

/--
@isnad1 id=measurab.1h3v.s4.935bbd859a6a from=translated src=- shape=e8101926 vocab=381439b0
-/
theorem measurableSet_dualTimeRelation {I : Set ℝ} (hI : MeasurableSet I) (a b : ℝ) :
    MeasurableSet (dualTimeRelation I a b) :=
  (measurableSet_eq_fun measurable_snd measurable_const).compl.inter
    ((measurableSet_dualPairParameters hI a b).preimage (measurable_fst.prodMk
      (measurable_dualTime measurable_const measurable_const measurable_snd measurable_fst)))

/--
@isnad1 id=measurab.3h4v.s7.89796c29ac92 from=translated src=- shape=33531a48 vocab=7bdedcb2
-/
theorem measurableSet_dualTimeRelation_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {p : X × (ℝ × ℝ) |
      p.2 ∈ dualTimeRelation {t | (p.1, t) ∈ I} (a p.1) (b p.1)} :=
  (measurableSet_eq_fun measurable_snd.snd measurable_const).compl.inter
    ((measurableSet_dualPairParameters_family hI ha hb).preimage
      (measurable_fst.prodMk (measurable_snd.fst.prodMk
        (measurable_dualTime (ha.comp measurable_fst) (hb.comp measurable_fst)
          measurable_snd.snd measurable_snd.fst))))

/--
@isnad1 id=eq.5h4v.s6.0b699b76079d from=translated src=- shape=76649fc1 vocab=e3418ca2
-/
theorem dualTimeRelation_section {I : Set ℝ} {a b t : ℝ} (hab : a ≠ b)
    (hta : t ≠ a) (htb : t ≠ b) (hIpos : 0 < volume I) (hIfin : volume I ≠ ∞) :
    Prod.mk t ⁻¹' dualTimeRelation I a b =
      dualScalar a b t '' (Prod.mk t ⁻¹' dualPairParameters I a b) := by
  exact (image_dualScalar hab hta htb (S := Prod.mk t ⁻¹' dualPairParameters I a b)
    (fun u hu ↦ (dualPairParameters_ne hIpos hIfin (p := (t, u)) hu).2.2.1)).symm

/--
@isnad1 id=and.7h5v.s8.d6c5328323de from=translated src=- shape=4daf97a9 vocab=0c34262f
-/
theorem dualTimeRelation_scalar_bounds {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) {p : ℝ × ℝ} (hp : p ∈ dualTimeRelation I a b) :
    δ * ((volume I).toReal / 100) ≤ |p.2| ∧ |p.2| ≤ (100 / (volume I).toReal) ^ 2 := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hne := dualPairParameters_ne hIpos hIfin hp.2
  have h := dualScalar_bounds hIunit hIpos ha hb hab hp.2
  rw [dualScalar_dualTime (dist_pos.mp (hδ.trans_le hab)) hp.1 hne.1 hne.2.1] at h
  exact ⟨h.1, h.2.1⟩

/--
@isnad1 id=le.7h5v.s8.4256815758db from=translated src=- shape=769dbd3b vocab=80c36dce
-/
theorem volume_dualTimeRelation_section_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) (t : ℝ) :
    ENNReal.ofReal (δ * ((volume I).toReal / 100)) *
      volume (Prod.mk t ⁻¹' dualPairParameters I a b) ≤
        volume (Prod.mk t ⁻¹' dualTimeRelation I a b) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  by_cases hQ : (Prod.mk t ⁻¹' dualPairParameters I a b).Nonempty
  · obtain ⟨u, hu⟩ := hQ
    have hne := dualPairParameters_ne hIpos hIfin hu
    have hab' := dist_pos.mp (hδ.trans_le hab)
    rw [dualTimeRelation_section hab' hne.1 hne.2.1 hIpos hIfin,
      volume_image_dualScalar hab' hne.1 hne.2.1
        ((measurableSet_dualPairParameters hI a b).preimage (by fun_prop))
        (fun _ hv ↦ (dualPairParameters_ne hIpos hIfin hv).2.2.1), ← setLIntegral_const]
    exact setLIntegral_mono'
      ((measurableSet_dualPairParameters hI a b).preimage (by fun_prop)) fun v hv ↦
        ENNReal.ofReal_le_ofReal (dualScalar_bounds hIunit hIpos ha hb hab hv).2.2
  · rw [Set.not_nonempty_iff_eq_empty.mp hQ, measure_empty, mul_zero]
    exact zero_le

/--
@isnad1 id=le.6h4v.s8.3ffb200abb29 from=translated src=- shape=15ee48d1 vocab=a39385da
-/
theorem dualTimeRelation_subset {I : Set ℝ} (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I)
    {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    dualTimeRelation I a b ⊆
      I ×ˢ Icc (-((100 / (volume I).toReal) ^ 2)) ((100 / (volume I).toReal) ^ 2) := by
  intro p hp
  exact ⟨(dualPairParameters_spec hp.2).1,
    abs_le.mp (dualTimeRelation_scalar_bounds hIunit hIpos ha hb hδ hab hp).2⟩

/--
@isnad1 id=ne.6h4v.s7.eb19c016dd7f from=translated src=- shape=79adb8d9 vocab=bfd3da5b
-/
theorem volume_dualTimeRelation_ne_top {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) : volume (dualTimeRelation I a b) ≠ ∞ := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  apply ne_top_of_le_ne_top _ (measure_mono (dualTimeRelation_subset hIunit hIpos ha hb hδ hab))
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  finiteness

/--
@isnad1 id=le.7h4v.s8.04d43adb4aba from=translated src=- shape=9240acfa vocab=1feabc4a
-/
theorem volume_dualTimeRelation_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 200) ≤ volume (dualTimeRelation I a b) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hmass : ENNReal.ofReal (δ * ((volume I).toReal / 100)) *
      volume (dualPairParameters I a b) ≤ volume (dualTimeRelation I a b) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_dualPairParameters hI a b),
      Measure.prod_apply (measurableSet_dualTimeRelation hI a b),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono (volume_dualTimeRelation_section_lower hI hIunit hIpos ha hb hδ hab)
  refine le_trans ?_ hmass
  calc
    _ = ENNReal.ofReal (δ * ((volume I).toReal / 100)) *
        ENNReal.ofReal ((volume I).toReal ^ 2 / 2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ _ := mul_le_mul le_rfl (half_square_le_volume_dualPairParameters hI hIfin a b)
      zero_le zero_le

end NKBesicovitch.Projection.Selection
