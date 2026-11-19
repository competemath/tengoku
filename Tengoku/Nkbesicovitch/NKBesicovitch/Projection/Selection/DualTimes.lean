/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Selection.DualRelation
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Selection.SeparatedTriples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Admissible times for each dual scalar

The time fiber of the dual relation is a Borel subset of the input time
set. Its measure varies measurably, including in measurable families of
time sets and base heights. Integrating these fiber measures recovers
the measure of the relation by Tonelli's theorem.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Times whose dual partner satisfies all five separation conditions.-/
noncomputable def dualTimes (I : Set ℝ) (a b c : ℝ) : Set ℝ :=
  {t | (t, c) ∈ dualTimeRelation I a b}

/--
@isnad1 id=and.1h5v.s8.29baa19c9ea3 from=translated src=- shape=91a3ee58 vocab=e98c7fd5
-/
theorem dualTimes_spec {I : Set ℝ} {a b c t : ℝ} (ht : t ∈ dualTimes I a b c) :
    c ≠ 0 ∧ t ∈ I ∧ dualTime a b c t ∈ I ∧
      (volume I).toReal / 100 ≤ dist t a ∧ (volume I).toReal / 100 ≤ dist t b ∧
      (volume I).toReal / 100 ≤ dist (dualTime a b c t) a ∧
      (volume I).toReal / 100 ≤ dist (dualTime a b c t) b ∧
      (volume I).toReal / 100 ≤ dist t (dualTime a b c t) :=
  ⟨ht.1, dualPairParameters_spec ht.2⟩

/--
@isnad1 id=le.0h4v.s4.998e56b351f5 from=translated src=- shape=5754517d vocab=da9374ff
-/
theorem dualTimes_subset (I : Set ℝ) (a b c : ℝ) : dualTimes I a b c ⊆ I :=
  fun _ ht ↦ (dualPairParameters_spec ht.2).1

/-- The base, inner time, and its dual form an admissible triple for the next corner node.
@isnad1 id=mem.2h5v.s6.9a042eaee59c from=translated src=- shape=add75310 vocab=81cbc32e
-/
theorem dualTimes_mem_separatedTriples {I : Set ℝ} {a b c t : ℝ} (ha : a ∈ I)
    (ht : t ∈ dualTimes I a b c) :
    ((a, t), dualTime a b c t) ∈ separatedTriples I ((volume I).toReal / 100) := by
  obtain ⟨_, htI, hdualI, hta, _, hdual_a, _, htdual⟩ := dualTimes_spec ht
  exact mem_separatedTriples.mpr ⟨ha, htI, hdualI,
    by simpa only [dist_comm] using hta, by simpa only [dist_comm] using hdual_a, htdual⟩

/--
@isnad1 id=measurab.1h4v.s4.2b9e4dc45e06 from=translated src=- shape=18073f35 vocab=8da95b66
-/
theorem measurableSet_dualTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c : ℝ) :
    MeasurableSet (dualTimes I a b c) :=
  (measurableSet_dualTimeRelation hI a b).preimage (by fun_prop)

/--
@isnad1 id=measurab.1h3v.s5.50a3817bcaab from=translated src=- shape=4a49d662 vocab=0dbe85ee
-/
theorem measurable_volume_dualTimes {I : Set ℝ} (hI : MeasurableSet I) (a b : ℝ) :
    Measurable (fun c ↦ volume (dualTimes I a b c)) :=
  measurable_measure_prodMk_right (measurableSet_dualTimeRelation hI a b)

/--
@isnad1 id=measurab.3h4v.s7.7ac92ec562d7 from=translated src=- shape=7bb608d9 vocab=7ae279e5
-/
theorem measurableSet_dualTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet {p : (X × ℝ) × ℝ |
      p.2 ∈ dualTimes {t | (p.1.1, t) ∈ I} (a p.1.1) (b p.1.1) p.1.2} := by
  change MeasurableSet ((fun p : (X × ℝ) × ℝ ↦ (p.1.1, (p.2, p.1.2))) ⁻¹'
    {q : X × (ℝ × ℝ) | q.2 ∈ dualTimeRelation {t | (q.1, t) ∈ I} (a q.1) (b q.1)})
  exact (measurableSet_dualTimeRelation_family hI ha hb).preimage
    (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))

/--
@isnad1 id=measurab.3h4v.s6.6d88ecc5c78d from=translated src=- shape=2dd7c9e3 vocab=abcd8d29
-/
theorem measurable_volume_dualTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p : X × ℝ ↦
      volume (dualTimes {t | (p.1, t) ∈ I} (a p.1) (b p.1) p.2)) :=
  measurable_measure_prodMk_left (measurableSet_dualTimes_family hI ha hb)

/--
@isnad1 id=eq.1h3v.s6.b11c6d349ff5 from=translated src=- shape=b2e53a92 vocab=e9628367
-/
theorem lintegral_volume_dualTimes {I : Set ℝ} (hI : MeasurableSet I) (a b : ℝ) :
    ∫⁻ c, volume (dualTimes I a b c) = volume (dualTimeRelation I a b) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_dualTimeRelation hI a b)]
  rfl

/--
@isnad1 id=le.6h4v.s8.886dabcdb836 from=translated src=- shape=cbd8256a vocab=2d6e15d2
-/
theorem support_volume_dualTimes_subset {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    Function.support (fun c ↦ volume (dualTimes I a b c)) ⊆
      Icc (-((100 / (volume I).toReal) ^ 2)) ((100 / (volume I).toReal) ^ 2) := by
  intro c hc
  obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hc
  exact (dualTimeRelation_subset hIunit hIpos ha hb hδ hab ht).2

end NKBesicovitch.Projection.Selection
