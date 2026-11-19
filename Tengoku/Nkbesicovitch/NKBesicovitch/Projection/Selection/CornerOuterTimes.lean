/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.Selection.CornerRelationMass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Outer time fibers for a common corner scalar

Every time in an outer fiber is separated from the two required base
heights and gives an inner coefficient in the dual reservoir. The outer
fibers and their measures are jointly measurable, and Tonelli identifies
their total mass with the compatible time-scalar relation.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection.Selection

/-- Separated outer times compatible with the fixed corner scalar.-/
noncomputable def cornerOuterTimes (I : Set ℝ) (a b c δ κ : ℝ) : Set ℝ :=
  {u | (u, κ) ∈ cornerTimeRelation I a b c δ}

/--
@isnad1 id=and.1h7v.s7.3869b28a7c10 from=translated src=- shape=af1d09c7 vocab=dbd68092
-/
theorem cornerOuterTimes_spec {I : Set ℝ} {a b c δ κ u : ℝ}
    (hu : u ∈ cornerOuterTimes I a b c δ κ) :
    u ∈ I ∧ (volume I).toReal / 100 ≤ dist u a ∧ (volume I).toReal / 100 ≤ dist u c ∧
      cornerInnerCoefficient a c κ u ∈ dualReservoir I b a δ :=
  cornerTimeRelation_spec hu

/--
@isnad1 id=le.0h6v.s4.2a0c7d815bff from=translated src=- shape=5afe3bc2 vocab=745a976b
-/
theorem cornerOuterTimes_subset (I : Set ℝ) (a b c δ κ : ℝ) :
    cornerOuterTimes I a b c δ κ ⊆ I := fun _ hu ↦ (cornerOuterTimes_spec hu).1

/--
@isnad1 id=measurab.1h6v.s4.a178b4952466 from=translated src=- shape=b65cc59a vocab=0d391657
-/
theorem measurableSet_cornerOuterTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c δ κ : ℝ) :
    MeasurableSet (cornerOuterTimes I a b c δ κ) :=
  (measurableSet_cornerTimeRelation hI a b c δ).preimage
    (f := fun u : ℝ ↦ (u, κ)) (by fun_prop)

/--
@isnad1 id=measurab.1h5v.s5.0180ce1b45b4 from=translated src=- shape=e3571912 vocab=ebed3046
-/
theorem measurable_volume_cornerOuterTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    Measurable (fun κ ↦ volume (cornerOuterTimes I a b c δ κ)) :=
  measurable_measure_prodMk_right (measurableSet_cornerTimeRelation hI a b c δ)

/--
@isnad1 id=measurab.5h6v.s7.7a3fef0e9f37 from=translated src=- shape=13169e96 vocab=456b02ff
-/
theorem measurableSet_cornerOuterTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    MeasurableSet {p : (X × ℝ) × ℝ | p.2 ∈ cornerOuterTimes {t | (p.1.1, t) ∈ I}
      (a p.1.1) (b p.1.1) (c p.1.1) (δ p.1.1) p.1.2} :=
  (measurableSet_cornerTimeRelation_family hI ha hb hc hδ).preimage
    (f := fun p : (X × ℝ) × ℝ ↦ (p.1.1, (p.2, p.1.2)))
    (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))

/--
@isnad1 id=measurab.5h6v.s7.f940d3c9ed0f from=translated src=- shape=882c6064 vocab=e20a4975
-/
theorem measurable_volume_cornerOuterTimes_family {X : Type*} [MeasurableSpace X]
    {I : Set (X × ℝ)} (hI : MeasurableSet I) {a b c δ : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hδ : Measurable δ) :
    Measurable (fun p : X × ℝ ↦ volume (cornerOuterTimes {t | (p.1, t) ∈ I}
      (a p.1) (b p.1) (c p.1) (δ p.1) p.2)) :=
  measurable_measure_prodMk_left (measurableSet_cornerOuterTimes_family hI ha hb hc hδ)

/--
@isnad1 id=eq.1h5v.s6.c3fdceed6819 from=translated src=- shape=c13c0d09 vocab=94c23c5d
-/
theorem lintegral_volume_cornerOuterTimes {I : Set ℝ} (hI : MeasurableSet I) (a b c δ : ℝ) :
    ∫⁻ κ, volume (cornerOuterTimes I a b c δ κ) = volume (cornerTimeRelation I a b c δ) := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm (measurableSet_cornerTimeRelation hI a b c δ)]
  rfl

/--
@isnad1 id=le.7h5v.s8.7dbf6be58cac from=translated src=- shape=88faad00 vocab=f21d49e5
-/
theorem support_volume_cornerOuterTimes_subset {I : Set ℝ} (hIunit : I ⊆ Icc 0 1)
    (hIpos : 0 < volume I) {a b c δ : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hc : c ∈ Icc 0 1) (hδ : 0 < δ) (hab : δ ≤ dist a b) :
    Function.support (fun κ ↦ volume (cornerOuterTimes I a b c δ κ)) ⊆
      Icc (-((100 / (volume I).toReal) ^ 3)) ((100 / (volume I).toReal) ^ 3) := by
  intro κ hκ
  obtain ⟨u, hu⟩ := nonempty_of_measure_ne_zero hκ
  exact abs_le.mp (cornerTimeRelation_scalar_bounds hIunit hIpos ha hb hc hδ hab hu).2.2

end NKBesicovitch.Projection.Selection
