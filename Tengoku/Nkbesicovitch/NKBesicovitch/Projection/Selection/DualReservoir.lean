/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Selection.DualTimes
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.PairRefinement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Keeping dual scalars with many admissible times

Retain scalars with at least `δ |I|⁵ / 8000000` of admissible time measure.
This is a jointly Borel selection. The discarded scalars account for at
most `δ |I|³ / 400` of the time-scalar measure, so at least that much
measure survives. Consequently the retained scalar set has measure at
least `δ |I|² / 400`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Dual scalars whose admissible time fiber meets the prescribed polynomial threshold.-/
noncomputable def dualReservoir (I : Set ℝ) (a b δ : ℝ) : Set ℝ :=
  {c | ENNReal.ofReal (δ * (volume I).toReal ^ 5 / 8000000) ≤ volume (dualTimes I a b c)}

/--
@isnad1 id=measurab.1h4v.s4.08dff75601ef from=translated src=- shape=18073f35 vocab=b4e969b2
-/
theorem measurableSet_dualReservoir {I : Set ℝ} (hI : MeasurableSet I) (a b δ : ℝ) :
    MeasurableSet (dualReservoir I a b δ) :=
  measurableSet_le measurable_const (measurable_volume_dualTimes hI a b)

/--
@isnad1 id=measurab.4h5v.s6.c422c301bad7 from=translated src=- shape=ee265c93 vocab=f71034e0
-/
theorem measurableSet_dualReservoir_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hδ : Measurable δ) :
    MeasurableSet {p : X × ℝ | p.2 ∈ dualReservoir {t | (p.1, t) ∈ I}
      (a p.1) (b p.1) (δ p.1)} := by
  have hL := (measurable_measure_prodMk_left (ν := volume) hI).ennreal_toReal
  exact measurableSet_le
    (((hδ.mul (hL.pow_const 5)).div_const 8000000).ennreal_ofReal.comp measurable_fst)
    (measurable_volume_dualTimes_family hI ha hb)

/--
@isnad1 id=and.7h5v.s8.5e19ef5e9ea6 from=translated src=- shape=d4f4ceed vocab=07666d17
-/
theorem dualReservoir_scalar_bounds {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) {c : ℝ} (hc : c ∈ dualReservoir I a b δ) :
    c ≠ 0 ∧ δ * ((volume I).toReal / 100) ≤ |c| ∧
      |c| ≤ (100 / (volume I).toReal) ^ 2 := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have hpos : 0 < volume (dualTimes I a b c) :=
    (ENNReal.ofReal_pos.mpr (by positivity)).trans_le hc
  obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hpos.ne'
  exact ⟨ht.1, dualTimeRelation_scalar_bounds hIunit hIpos ha hb hδ hab ht⟩

/--
@isnad1 id=ne.6h4v.s7.02467085b28d from=translated src=- shape=d49e8a5a vocab=7f4d6752
-/
theorem volume_dualReservoir_ne_top {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) : volume (dualReservoir I a b δ) ≠ ∞ := by
  have hsub : dualReservoir I a b δ ⊆
      Icc (-((100 / (volume I).toReal) ^ 2)) ((100 / (volume I).toReal) ^ 2) :=
    fun _ hc ↦ abs_le.mp (dualReservoir_scalar_bounds hIunit hIpos ha hb hδ hab hc).2.2
  exact ne_top_of_le_ne_top (by simp) (measure_mono hsub)

/--
@isnad1 id=le.7h4v.s8.d6f19995569b from=translated src=- shape=909abdb9 vocab=3de1842d
-/
theorem lintegral_dualTimes_discarded_le {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    (∫⁻ c in (dualReservoir I a b δ)ᶜ, volume (dualTimes I a b c)) ≤
      ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 400) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  have hL := ENNReal.toReal_pos hIpos.ne' hIfin
  have h := setLIntegral_lt_le_mul_measure (μ := volume) (measurable_volume_dualTimes hI a b)
    (support_volume_dualTimes_subset hIunit hIpos ha hb hδ hab)
    (ENNReal.ofReal (δ * (volume I).toReal ^ 5 / 8000000))
  have hcomp : (dualReservoir I a b δ)ᶜ =
      {c | volume (dualTimes I a b c) < ENNReal.ofReal (δ * (volume I).toReal ^ 5 / 8000000)} := by
    ext c
    simp only [dualReservoir, mem_compl_iff, mem_ofPred_eq, not_le]
  rw [hcomp]
  refine h.trans_eq ?_
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

/--
@isnad1 id=le.7h4v.s7.38fb3833e844 from=translated src=- shape=2b550c64 vocab=95444580
-/
theorem lintegral_dualTimes_retained_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 400) ≤
      ∫⁻ c in dualReservoir I a b δ, volume (dualTimes I a b c) := by
  apply ENNReal.le_of_add_le_add_left (a := ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 400))
    ENNReal.ofReal_ne_top
  calc
    _ = ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 200) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ volume (dualTimeRelation I a b) :=
      volume_dualTimeRelation_lower hI hIunit hIpos ha hb hδ hab
    _ = (∫⁻ c in dualReservoir I a b δ, volume (dualTimes I a b c)) +
        ∫⁻ c in (dualReservoir I a b δ)ᶜ, volume (dualTimes I a b c) :=
      (lintegral_volume_dualTimes hI a b).symm.trans
        (lintegral_add_compl _ (measurableSet_dualReservoir hI a b δ)).symm
    _ ≤ (∫⁻ c in dualReservoir I a b δ, volume (dualTimes I a b c)) +
        ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 400) :=
      add_le_add le_rfl (lintegral_dualTimes_discarded_le hI hIunit hIpos ha hb hδ hab)
    _ = _ := add_comm _ _

/--
@isnad1 id=le.7h4v.s7.f151d90a53d0 from=translated src=- shape=4182f436 vocab=0f5066b3
-/
theorem volume_dualReservoir_lower {I : Set ℝ} (hI : MeasurableSet I)
    (hIunit : I ⊆ Icc 0 1) (hIpos : 0 < volume I) {a b δ : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    ENNReal.ofReal (δ * (volume I).toReal ^ 2 / 400) ≤ volume (dualReservoir I a b δ) := by
  have hIfin : volume I ≠ ∞ := ne_top_of_le_ne_top (by simp) (measure_mono hIunit)
  apply (ENNReal.mul_le_mul_iff_right hIpos.ne' hIfin).mp
  calc
    _ = ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 400) := by
      conv_lhs => arg 1; rw [← ENNReal.ofReal_toReal hIfin]
      rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      congr 1
      ring
    _ ≤ ∫⁻ c in dualReservoir I a b δ, volume (dualTimes I a b c) :=
      lintegral_dualTimes_retained_lower hI hIunit hIpos ha hb hδ hab
    _ ≤ volume I * volume (dualReservoir I a b δ) := by
      rw [← setLIntegral_const]
      exact setLIntegral_mono measurable_const fun c _ ↦ measure_mono (dualTimes_subset I a b c)

/-- The quantitative dual-pair reservoir, with explicit polynomial measure bounds.
@isnad1 id=and.7h4v.s9.3ebfe5e0bb77 from=translated src=- shape=2e6a3f27 vocab=efbcb447
-/
theorem dualReservoir_spec {I : Set ℝ} (hI : MeasurableSet I) (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    MeasurableSet (dualReservoir I a b δ) ∧
      ENNReal.ofReal (δ * (volume I).toReal ^ 2 / 400) ≤ volume (dualReservoir I a b δ) ∧
      ENNReal.ofReal (δ * (volume I).toReal ^ 3 / 400) ≤
        (∫⁻ c in dualReservoir I a b δ, volume (dualTimes I a b c)) ∧
      ∀ c ∈ dualReservoir I a b δ, c ≠ 0 ∧
        δ * ((volume I).toReal / 100) ≤ |c| ∧ |c| ≤ (100 / (volume I).toReal) ^ 2 ∧
        MeasurableSet (dualTimes I a b c) ∧ dualTimes I a b c ⊆ I ∧
        ENNReal.ofReal (δ * (volume I).toReal ^ 5 / 8000000) ≤ volume (dualTimes I a b c) := by
  refine ⟨measurableSet_dualReservoir hI a b δ,
    volume_dualReservoir_lower hI hIunit hIpos (hIunit ha) (hIunit hb) hδ hab,
    lintegral_dualTimes_retained_lower hI hIunit hIpos (hIunit ha) (hIunit hb) hδ hab, ?_⟩
  intro c hc
  obtain ⟨hc₀, hc₁, hc₂⟩ :=
    dualReservoir_scalar_bounds hIunit hIpos (hIunit ha) (hIunit hb) hδ hab hc
  exact ⟨hc₀, hc₁, hc₂, measurableSet_dualTimes hI a b c, dualTimes_subset I a b c, hc⟩

end NKBesicovitch.Projection.Selection
