/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.SimplexExponentialLaw
public import Tengoku.LeanPool.LeanPool.Feige.GeometryBridge
public import Tengoku.LeanPool.LeanPool.Feige.NormalizedExponentialProbability
import Tengoku.LeanPool.LeanPool.Feige.NNRealExponentialLaw

/-!
# Event bridge for the exponential and simplex statistics

This file records the deterministic normalization identity between the
simplex statistic in (2.1) and the internal exponential representation, in
the `NNReal` coordinate model used by `expProductMeasure`.
-/

@[expose] public section

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory

namespace Feige

variable {n : ℕ}

/--
@isnad1 id=eq.0h0v.s4.d5c98e02b23d from=translated src=- shape=25d9d552 vocab=ba1f6e9d
-/
theorem expMeasure_one_eq_withDensity_unitExponentialDensity :
    expMeasure 1 = volume.withDensity
      (fun x ↦ ENNReal.ofReal (unitExponentialDensity x)) := by
  unfold expMeasure gammaMeasure
  congr 1
  funext x
  unfold gammaPDF gammaPDFReal unitExponentialDensity
  by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]

/-- Binary density-product bridge used in the finite-dimensional
induction.
@isnad1 id=eq.2h4v.s7.fdf989a86ce2 from=translated src=- shape=138043c1 vocab=ccc00f9c
-/
theorem prod_withDensity_eq_volume_withDensity
    {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure β)]
    {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ((volume : Measure α).withDensity f).prod
        ((volume : Measure β).withDensity g) =
      ((volume : Measure α).prod (volume : Measure β)).withDensity
        (fun z ↦ f z.1 * g z.2) := by
  rw [prod_withDensity hf hg]

/-- Transporting a density through a measure-preserving measurable
equivalence transports the underlying measure and composes the density
with the equivalence.
@isnad1 id=eq.2h6v.s7.d9b19c9d6e8d from=translated src=- shape=ca256b24 vocab=b047f7a9
-/
theorem MeasurePreserving.map_withDensity_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    (T : α ≃ᵐ β) (hT : MeasurePreserving T μ ν)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    Measure.map T (μ.withDensity (f ∘ T)) =
      ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply T.measurable hs]
  rw [withDensity_apply _ (hs.preimage T.measurable)]
  rw [withDensity_apply _ hs]
  simpa only [Function.comp_apply] using
    hT.setLIntegral_comp_preimage hs hf

/-- One induction step: adjoining an independent unit exponential to a
finite-dimensional density multiplies the joint density.
@isnad1 id=eq.1h2v.s6.e6b2f4c4f769 from=translated src=- shape=137c2333 vocab=9c94641b
-/
theorem expMeasure_prod_withDensity
    {β : Type*} [MeasureSpace β]
    [SFinite (volume : Measure β)]
    {g : β → ℝ≥0∞} (hg : Measurable g) :
    (expMeasure 1).prod ((volume : Measure β).withDensity g) =
      ((volume : Measure ℝ).prod (volume : Measure β)).withDensity
        (fun z ↦ ENNReal.ofReal (unitExponentialDensity z.1) * g z.2) := by
  rw [expMeasure_one_eq_withDensity_unitExponentialDensity]
  exact prod_withDensity_eq_volume_withDensity
    (by
      apply Measurable.ennreal_ofReal
      unfold unitExponentialDensity
      exact (Real.measurable_exp.comp measurable_neg).indicator
        measurableSet_Ici) hg

/-- The joint unit-exponential density on `Fin n → ℝ`. -/
noncomputable def finExponentialDensity (n : ℕ) :
    (Fin n → ℝ) → ℝ≥0∞ :=
  fun x ↦ ∏ i, ENNReal.ofReal (unitExponentialDensity (x i))

/--
@isnad1 id=measurab.0h1v.s4.9ed5d3187c9b from=translated src=- shape=e6b716cb vocab=a4fc65b9
-/
theorem measurable_finExponentialDensity (n : ℕ) :
    Measurable (finExponentialDensity n) := by
  unfold finExponentialDensity
  apply Finset.measurable_fun_prod
  intro i _
  apply Measurable.ennreal_ofReal
  unfold unitExponentialDensity
  exact ((Real.measurable_exp.comp measurable_neg).comp
    (measurable_pi_apply i)).indicator
      (measurableSet_Ici.preimage (measurable_pi_apply i))

/-- The finite product of unit exponential laws has the product of the
one-dimensional exponential densities with respect to Lebesgue volume.
@isnad1 id=eq.0h1v.s6.92bd362b6acf from=translated src=- shape=581016f3 vocab=e9437392
-/
theorem pi_expMeasure_eq_withDensity (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ expMeasure 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (finExponentialDensity n) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  induction n with
  | zero =>
      have hpi :
          Measure.pi (fun _ : Fin 0 ↦ expMeasure 1) =
            (volume : Measure (Fin 0 → ℝ)) := by
        rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ expMeasure 1),
          Measure.volume_pi_eq_dirac]
      have hd : finExponentialDensity 0 = 1 := by
        funext x
        simp [finExponentialDensity]
      rw [hpi, hd, withDensity_one]
  | succ n ih =>
      let T : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hExp :
          MeasurePreserving T
            (Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1))
            ((expMeasure 1).prod
              (Measure.pi (fun _ : Fin n ↦ expMeasure 1))) := by
        simpa [T] using
          (measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ expMeasure 1) 0)
      have hVol :
          MeasurePreserving T
            (volume : Measure (Fin (n + 1) → ℝ))
            (volume : Measure (ℝ × (Fin n → ℝ))) := by
        simpa [T] using
          (volume_preserving_piFinSuccAbove
            (fun _ : Fin (n + 1) ↦ ℝ) 0)
      have hdensity :
          (fun z : ℝ × (Fin n → ℝ) ↦
              ENNReal.ofReal (unitExponentialDensity z.1) *
                finExponentialDensity n z.2) =
            finExponentialDensity (n + 1) ∘ T.symm := by
        funext z
        simp [finExponentialDensity, T,
          MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.prod_univ_succ]
      calc
        Measure.pi (fun _ : Fin (n + 1) ↦ expMeasure 1) =
            Measure.map T.symm
              ((expMeasure 1).prod
                (Measure.pi (fun _ : Fin n ↦ expMeasure 1))) := by
          rw [← hExp.map_eq]
          exact (MeasurableEquiv.map_symm_map T).symm
        _ = Measure.map T.symm
              ((expMeasure 1).prod
                ((volume : Measure (Fin n → ℝ)).withDensity
                  (finExponentialDensity n))) := by rw [ih]
        _ = Measure.map T.symm
              ((volume : Measure (ℝ × (Fin n → ℝ))).withDensity
                (fun z ↦
                  ENNReal.ofReal (unitExponentialDensity z.1) *
                    finExponentialDensity n z.2)) := by
          rw [expMeasure_prod_withDensity
            (measurable_finExponentialDensity n)]
          rw [Measure.volume_eq_prod]
        _ = Measure.map T.symm
              ((volume : Measure (ℝ × (Fin n → ℝ))).withDensity
                (finExponentialDensity (n + 1) ∘ T.symm)) := by
          rw [hdensity]
        _ = (volume : Measure (Fin (n + 1) → ℝ)).withDensity
              (finExponentialDensity (n + 1)) := by
          exact MeasurePreserving.map_withDensity_equiv T.symm hVol.symm
            (measurable_finExponentialDensity (n + 1))

/--
@isnad1 id=eq.0h2v.s5.ef7e429834e7 from=translated src=- shape=722c2e96 vocab=3149434e
-/
theorem productExponentialDensity_eq_ofReal_joint
    (e : ℝ × (Fin n → ℝ)) :
    ENNReal.ofReal (unitExponentialDensity e.1) *
        finExponentialDensity n e.2 =
      ENNReal.ofReal (jointUnitExponentialDensity e) := by
  unfold finExponentialDensity jointUnitExponentialDensity
  rw [ENNReal.ofReal_mul]
  · rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    by_cases hi : 0 ≤ e.2 i
    · simp [unitExponentialDensity, Set.indicator, hi,
        (Real.exp_pos (-e.2 i)).le]
    · simp [unitExponentialDensity, Set.indicator, hi]
  · unfold unitExponentialDensity
    by_cases h0 : 0 ≤ e.1
    · simp [Set.indicator, h0, (Real.exp_pos (-e.1)).le]
    · simp [Set.indicator, h0]

/--
@isnad1 id=eq.0h1v.s6.28429be518d5 from=translated src=- shape=b8928d6a vocab=d055473d
-/
theorem expMeasure_prod_pi_eq_realExponentialProductMeasure :
    (expMeasure 1).prod
        (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) =
      realExponentialProductMeasure (n := n) := by
  rw [pi_expMeasure_eq_withDensity n]
  rw [expMeasure_prod_withDensity
    (measurable_finExponentialDensity n)]
  rw [← Measure.volume_eq_prod]
  unfold realExponentialProductMeasure
  rw [← withDensity_indicator
    (μ := (volume : Measure (ℝ × (Fin n → ℝ))))
    isMeasurableSet_positiveExponentialOrthant]
  apply withDensity_congr_ae
  have hne : ∀ᵐ e : ℝ × (Fin n → ℝ) ∂volume,
      e ≠ (0, fun _ ↦ 0) := by
    rw [ae_iff]
    simpa using
      (volume_singleton_zeroExponentialVector (n := n))
  filter_upwards [hne] with e hne
  rw [productExponentialDensity_eq_ofReal_joint]
  by_cases hnonneg : 0 ≤ e.1 ∧ ∀ i, 0 ≤ e.2 i
  · have ht := nonnegative_nonzero_exponentialTotal_pos
      hnonneg.1 hnonneg.2 hne
    have hm : e ∈ positiveExponentialOrthant (n := n) :=
      ⟨hnonneg.1, hnonneg.2, ht⟩
    rw [Set.indicator_of_mem hm]
    rw [jointUnitExponentialDensity_eq_exp_neg_total
      e hnonneg.1 hnonneg.2]
  · have hnmem : e ∉ positiveExponentialOrthant (n := n) := by
      intro he
      exact hnonneg ⟨he.1, he.2.1⟩
    simp only [Set.indicator, ite_eq_right hnmem]
    have hjoint : jointUnitExponentialDensity e = 0 := by
      apply jointUnitExponentialDensity_eq_zero_of_neg
      by_cases hfirst : 0 ≤ e.1
      · right
        push Not at hnonneg
        exact hnonneg hfirst
      · exact Or.inl (lt_of_not_ge hfirst)
    simp [hjoint]

/-- Coerce every coordinate of an `NNReal` vector to a real number. -/
def nnrealOptionToRealOption
    (e : Option (Fin n) → NNReal) : Option (Fin n) → ℝ :=
  fun i ↦ (e i : ℝ)

/--
@isnad1 id=measurab.0h1v.s5.6ff060e95b5a from=translated src=- shape=38520e02 vocab=9dc53ed3
-/
theorem measurable_nnrealOptionToRealOption :
    Measurable (nnrealOptionToRealOption (n := n)) := by
  unfold nnrealOptionToRealOption
  fun_prop

/--
@isnad1 id=eq.0h1v.s7.8a2200c1b813 from=translated src=- shape=9d9145f9 vocab=e73d76fb
-/
theorem map_realOptionProductMeasure :
    Measure.map (optionVectorToProduct (n := n))
        (Measure.pi (fun _ : Option (Fin n) ↦ expMeasure 1)) =
      (expMeasure 1).prod
        (Measure.pi (fun _ : Fin n ↦ expMeasure 1)) := by
  let : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let q : (Option (Fin n) → ℝ) ≃ᵐ
      ((Fin n → ℝ) × ℝ) :=
    MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin n) ↦ ℝ)
  have hq :
      Measure.map q
          (Measure.pi (fun _ : Option (Fin n) ↦ expMeasure 1)) =
        (Measure.pi (fun _ : Fin n ↦ expMeasure 1)).prod
          (expMeasure 1) := by
    rw [q.map_apply_eq_iff_map_symm_apply_eq]
    simpa [q] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Fin n) ↦ expMeasure 1)).symm
  rw [show optionVectorToProduct (n := n) = Prod.swap ∘ q by rfl]
  rw [← Measure.map_map measurable_swap q.measurable]
  rw [hq, Measure.prod_swap]

/-- The total mass of an optional-indexed nonnegative vector. -/
def nnrealExponentialTotal (e : Option (Fin n) → NNReal) : ℝ :=
  (e none : ℝ) + ∑ i, (e (some i) : ℝ)

/-- Normalize the finite coordinates by the total exponential mass. -/
noncomputable def nnrealNormalizedCoordinates
    (e : Option (Fin n) → NNReal) : Fin n → ℝ :=
  fun i ↦ (e (some i) : ℝ) / nnrealExponentialTotal e

/--
@isnad1 id=measurab.0h1v.s4.82e4ce4dab4f from=translated src=- shape=755d2504 vocab=d90aeb69
-/
theorem measurable_nnrealExponentialTotal :
    Measurable (nnrealExponentialTotal :
      (Option (Fin n) → NNReal) → ℝ) := by
  unfold nnrealExponentialTotal
  fun_prop

/--
@isnad1 id=mem.1h2v.s5.261f61d1d1b1 from=translated src=- shape=e37efed1 vocab=410cdc00
-/
theorem nnrealNormalizedCoordinates_mem_fullSimplex
    {e : Option (Fin n) → NNReal}
    (ht : 0 < nnrealExponentialTotal e) :
    nnrealNormalizedCoordinates e ∈ fullSimplex (Fin n) := by
  rw [mem_fullSimplex_iff]
  constructor
  · intro i
    exact div_nonneg (e (some i)).coe_nonneg ht.le
  · unfold nnrealNormalizedCoordinates nnrealExponentialTotal
    rw [← Finset.sum_div]
    apply (div_le_one ht).2
    exact le_add_of_nonneg_left (e none).coe_nonneg

/-- On every nonzero exponential vector, the event defining `dirichletK`
is exactly the simplex halfspace event after normalization.
@isnad1 id=iff.1h3v.s6.a60aec33c98b from=translated src=- shape=4cf2e861 vocab=232c99cd
-/
theorem mem_kEvent_iff_normalized_simplex_event
    (y : Fin n → ℝ) {e : Option (Fin n) → NNReal}
    (ht : 0 < nnrealExponentialTotal e) :
    e ∈ kEvent y ↔
      simplexLinearForm y (nnrealNormalizedCoordinates e) ≤ 1 := by
  unfold kEvent simplexLinearForm nnrealNormalizedCoordinates
  change
    (∑ i, (y i - 1) * (e (some i) : ℝ)) ≤ (e none : ℝ) ↔
      ∑ i, y i * ((e (some i) : ℝ) / nnrealExponentialTotal e) ≤ 1
  have hsum :
      ∑ i, y i * ((e (some i) : ℝ) / nnrealExponentialTotal e) =
        (∑ i, y i * (e (some i) : ℝ)) /
          nnrealExponentialTotal e := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  rw [div_le_one ht]
  unfold nnrealExponentialTotal
  constructor <;> intro h
  · calc
      ∑ i, y i * (e (some i) : ℝ) =
          ∑ i, ((y i - 1) * (e (some i) : ℝ) +
            (e (some i) : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, (y i - 1) * (e (some i) : ℝ)) +
          ∑ i, (e (some i) : ℝ) := by
            rw [Finset.sum_add_distrib]
      _ ≤ (e none : ℝ) + ∑ i, (e (some i) : ℝ) := by
        linarith
  · have :
        ∑ i, (y i - 1) * (e (some i) : ℝ) =
          (∑ i, y i * (e (some i) : ℝ)) -
            ∑ i, (e (some i) : ℝ) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    change ∑ i, (y i - 1) * (e (some i) : ℝ) ≤ (e none : ℝ)
    rw [this]
    linarith

/--
@isnad1 id=eq.0h2v.s4.74fd827bf1d8 from=translated src=- shape=ba559eb4 vocab=2d74d8d7
-/
theorem normalizedCoordinates_realProduct_comp
    (e : Option (Fin n) → NNReal) :
    normalizedExponentialCoordinates
        (optionVectorToProduct (nnrealOptionToRealOption e)) =
      nnrealNormalizedCoordinates e := by
  rfl

/--
@isnad1 id=iff.0h3v.s5.54bd9fa0cac2 from=translated src=- shape=b489c324 vocab=2b6c3300
-/
theorem mem_kEvent_iff_normalized_simplex_event'
    (y : Fin n → ℝ) (e : Option (Fin n) → NNReal) :
    e ∈ kEvent y ↔
      simplexLinearForm y (nnrealNormalizedCoordinates e) ≤ 1 := by
  by_cases ht : 0 < nnrealExponentialTotal e
  · exact mem_kEvent_iff_normalized_simplex_event y ht
  · have htotal : nnrealExponentialTotal e = 0 := by
      apply le_antisymm
      · exact le_of_not_gt ht
      · unfold nnrealExponentialTotal
        positivity
    have hnone : e none = 0 := by
      have hnonneg : 0 ≤ ∑ i, (e (some i) : ℝ) :=
        Finset.sum_nonneg fun i _ ↦ (e (some i)).coe_nonneg
      rw [← NNReal.coe_eq_zero]
      unfold nnrealExponentialTotal at htotal
      exact le_antisymm (by linarith) (e none).coe_nonneg
    have hsome : ∀ i, e (some i) = 0 := by
      intro i
      apply NNReal.eq
      have hsum : ∑ j, (e (some j) : ℝ) = 0 := by
        unfold nnrealExponentialTotal at htotal
        simp only [hnone, NNReal.coe_zero, zero_add] at htotal
        exact htotal
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ (e (some j)).coe_nonneg)).mp hsum i
          (Finset.mem_univ i)
    simp [kEvent, simplexLinearForm, nnrealNormalizedCoordinates,
      htotal, hnone, hsome]

end Feige
