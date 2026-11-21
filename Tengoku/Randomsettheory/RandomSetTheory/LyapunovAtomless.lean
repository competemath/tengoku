/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.Probability.CDF
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Atomlessness and scalar Lyapunov convexity

Mathlib's `NullSingletonClass` is weaker than genuine atomlessness on an
arbitrary measurable space.  On the real Borel line, however, a finite
measure without point masses is exactly divisible.  This file proves that
fact from continuity of the cumulative distribution function and develops
its consequences for Lyapunov convexity.

The main results are:

* `exists_measurable_subset_measureReal_eq_mul`: exact divisibility of a
  finite real Borel measure;
* `isAtomlessMeasure_of_nullSingletonClass_real`: the bridge from Mathlib's
  point-mass class to the project's genuine atomlessness property on `ℝ`;
* `hasLyapunovConvexity_real_of_nullSingletonClass`: exact scalar Lyapunov
  convexity, without assuming that the base measure is finite;
* `SimpleFunc.exists_setIntegral_eq_smul_of_nullSingletonClass`: exact
  vector-valued proportional splitting for simple functions;
* invariance of Lyapunov convexity under measurable equivalences.

The full finite-dimensional vector-valued Lyapunov theorem for arbitrary
integrable functions is strictly stronger than the results available in
Mathlib.  The simple-function theorem below isolates the exact remaining
closure/compactness passage without adding an axiom.
-/

open MeasureTheory Set Filter

noncomputable section

namespace RandomSetTheory

/-! ## Continuous atomless cumulative distributions -/

/-- The CDF of a probability measure on `ℝ` without point masses is
continuous.  Mathlib provides right-continuity; vanishing singleton masses
identify the left limit with the value.
@isnad1 id=continuo.0h1v.s5.336c0857d5c5 from=translated src=- shape=d183f2f7 vocab=9b9d1207
-/
theorem continuous_cdf_of_nullSingletonClass (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    Continuous (ProbabilityTheory.cdf mu) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(ProbabilityTheory.monotone_cdf mu).continuousAt_iff_leftLim_eq_rightLim,
    (ProbabilityTheory.cdf mu).rightLim_eq]
  apply le_antisymm
  · exact (ProbabilityTheory.monotone_cdf mu).leftLim_le le_rfl
  · have hzero : ENNReal.ofReal
        (ProbabilityTheory.cdf mu x - Function.leftLim (ProbabilityTheory.cdf mu) x) = 0 := by
      rw [← (ProbabilityTheory.cdf mu).measure_singleton x,
        ProbabilityTheory.measure_cdf mu, measure_singleton]
    have hnonpos : ProbabilityTheory.cdf mu x -
        Function.leftLim (ProbabilityTheory.cdf mu) x ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hzero
    linarith

/-- Every value strictly between zero and one is attained by the CDF of an
atomless real probability measure.
@isnad1 id=ex.2h2v.s6.b09009f9cd8c from=translated src=- shape=de203eec vocab=a74bf0e0
-/
theorem exists_Iic_measure_eq_of_between (mu : Measure ℝ)
    [IsProbabilityMeasure mu] [NullSingletonClass mu]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ x : ℝ, mu (Iic x) = ENNReal.ofReal a := by
  have hlow : ∀ᶠ x in atBot, ProbabilityTheory.cdf mu x < a :=
    (ProbabilityTheory.tendsto_cdf_atBot mu).eventually_lt_const ha0
  have hupp : ∀ᶠ x in atTop, a < ProbabilityTheory.cdf mu x :=
    (ProbabilityTheory.tendsto_cdf_atTop mu).eventually_const_lt ha1
  obtain ⟨xlow, hxlow⟩ := hlow.exists
  obtain ⟨xupp, hxupp⟩ := hupp.exists
  obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge
    (continuous_cdf_of_nullSingletonClass mu)
    ⟨xlow, hxlow.le⟩ ⟨xupp, hxupp.le⟩
  refine ⟨x, ?_⟩
  rw [← hx, ProbabilityTheory.ofReal_cdf]

/-! ## Exact divisibility of finite real Borel measures -/

/-- A finite Borel measure on `ℝ` without point masses has a measurable
set carrying any prescribed fraction of its total mass.
@isnad1 id=ex.2h2v.s6.a5cab95645f0 from=translated src=- shape=7bf06e02 vocab=8d6a5338
-/
theorem exists_measurable_measureReal_eq_mul_univ (nu : Measure ℝ)
    [IsFiniteMeasure nu] [NullSingletonClass nu]
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ A : Set ℝ, MeasurableSet A ∧ nu.real A = a * nu.real univ := by
  rcases ha0.eq_or_lt with rfl | ha0
  · exact ⟨∅, MeasurableSet.empty, by simp⟩
  rcases ha1.eq_or_lt with rfl | ha1
  · exact ⟨univ, MeasurableSet.univ, by simp⟩
  by_cases hnu : nu = 0
  · subst nu
    exact ⟨∅, MeasurableSet.empty, by simp⟩
  let nuf : FiniteMeasure ℝ := ⟨nu, inferInstance⟩
  have hnuf : nuf ≠ 0 := by
    intro h
    apply hnu
    have hc := congrArg FiniteMeasure.toMeasure h
    simpa [nuf] using hc
  let P : ProbabilityMeasure ℝ := nuf.normalize
  letI : NullSingletonClass (P : Measure ℝ) :=
    ⟨fun x ↦ by
      rw [show (P : Measure ℝ) = nuf.mass⁻¹ • (nuf : Measure ℝ) by
        exact nuf.toMeasure_normalize_eq_of_nonzero hnuf]
      rw [Measure.smul_apply]
      have hx0 : (nuf : Measure ℝ) {x} = 0 := by
        change nu {x} = 0
        exact measure_singleton x
      rw [hx0]
      simp⟩
  obtain ⟨x, hx⟩ := exists_Iic_measure_eq_of_between
    (P : Measure ℝ) ha0 ha1
  refine ⟨Iic x, measurableSet_Iic, ?_⟩
  have hxreal : (P : Measure ℝ).real (Iic x) = a := by
    rw [measureReal_def, hx, ENNReal.toReal_ofReal ha0.le]
  have hxP : (P (Iic x) : ℝ) = a := by simpa using hxreal
  change (nuf (Iic x) : ℝ) = a * (nuf univ : ℝ)
  calc
    (nuf (Iic x) : ℝ) = (nuf.mass : ℝ) * (P (Iic x) : ℝ) := by
      exact_mod_cast nuf.self_eq_mass_mul_normalize (Iic x)
    _ = (nuf.mass : ℝ) * a := by rw [hxP]
    _ = a * (nuf univ : ℝ) := by
      simp only [FiniteMeasure.mass]
      ring

/-- Exact divisibility inside an arbitrary measurable set.
@isnad1 id=ex.3h3v.s6.e24acb70a4e4 from=translated src=- shape=ff4558fd vocab=d29c1e48
-/
theorem exists_measurable_subset_measureReal_eq_mul (nu : Measure ℝ)
    [IsFiniteMeasure nu] [NullSingletonClass nu]
    {s : Set ℝ} (hs : MeasurableSet s)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ A : Set ℝ, A ⊆ s ∧ MeasurableSet A ∧
      nu.real A = a * nu.real s := by
  letI : IsFiniteMeasure (nu.restrict s) :=
    isFiniteMeasure_restrict.mpr (measure_ne_top nu s)
  obtain ⟨A, hA, hmeasure⟩ :=
    exists_measurable_measureReal_eq_mul_univ (nu.restrict s) ha0 ha1
  rw [measureReal_restrict_apply hA, measureReal_restrict_apply_univ] at hmeasure
  refine ⟨A ∩ s, inter_subset_right, hA.inter hs, ?_⟩
  simpa using hmeasure

/-- On the real Borel line, Mathlib's `NullSingletonClass` implies the
project's genuine atomlessness property for finite measures.
@isnad1 id=isatomle.0h1v.s4.626ef484a378 from=translated src=- shape=3305e152 vocab=bf52574b
-/
theorem isAtomlessMeasure_of_nullSingletonClass_real (nu : Measure ℝ)
    [IsFiniteMeasure nu] [NullSingletonClass nu] :
    IsAtomlessMeasure nu := by
  intro s hs hspos
  obtain ⟨A, hAs, hA, hmeasure⟩ :=
    exists_measurable_subset_measureReal_eq_mul nu hs
      (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨A, hAs, hA, ?_, ?_⟩
  · apply (ENNReal.toReal_lt_toReal (by simp) (measure_ne_top nu A)).mp
    change 0 < nu.real A
    rw [hmeasure]
    have hsreal : 0 < nu.real s :=
      ENNReal.toReal_pos hspos.ne' (measure_ne_top nu s)
    positivity
  · apply (ENNReal.toReal_lt_toReal (measure_ne_top nu A)
      (measure_ne_top nu s)).mp
    change nu.real A < nu.real s
    rw [hmeasure]
    have hsreal : 0 < nu.real s :=
      ENNReal.toReal_pos hspos.ne' (measure_ne_top nu s)
    linarith

/-! ## Exact scalar splitting of integrals -/

/-- A measurable integrable real function admits a measurable set carrying
any prescribed fraction of its integral.  Positive and negative parts are
split independently using the exact divisibility theorem.
@isnad1 id=ex.4h3v.s7.2b03325f9468 from=translated src=- shape=51a064d5 vocab=9307fa93
-/
theorem exists_setIntegral_eq_mul_real_of_measurable
    (mu : Measure ℝ) [NullSingletonClass mu]
    {f : ℝ → ℝ} (hf : Integrable f mu) (hfm : Measurable f)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ A : Set ℝ, MeasurableSet A ∧
      (∫ x in A, f x ∂mu) = a * ∫ x, f x ∂mu := by
  let P : Set ℝ := {x | 0 ≤ f x}
  let N : Set ℝ := {x | f x < 0}
  have hP : MeasurableSet P := hfm measurableSet_Ici
  have hN : MeasurableSet N := hfm measurableSet_Iio
  let mup : Measure ℝ := mu.withDensity (fun x ↦ ENNReal.ofReal (f x))
  let mun : Measure ℝ := mu.withDensity (fun x ↦ ENNReal.ofReal (-f x))
  letI : IsFiniteMeasure mup :=
    isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  letI : IsFiniteMeasure mun :=
    isFiniteMeasure_withDensity hf.neg.lintegral_lt_top.ne
  obtain ⟨Ap, hApP, hAp, hApmeasure⟩ :=
    exists_measurable_subset_measureReal_eq_mul mup hP ha0 ha1
  obtain ⟨An, hAnN, hAn, hAnmeasure⟩ :=
    exists_measurable_subset_measureReal_eq_mul mun hN ha0 ha1
  have hmup_compl : mup Pᶜ = 0 := by
    change mu.withDensity (fun x ↦ ENNReal.ofReal (f x)) Pᶜ = 0
    rw [withDensity_apply _ hP.compl]
    apply setLIntegral_eq_zero hP.compl
    intro x hx
    simp only [Pi.zero_apply]
    apply ENNReal.ofReal_eq_zero.mpr
    exact le_of_not_ge hx
  have hmun_compl : mun Nᶜ = 0 := by
    change mu.withDensity (fun x ↦ ENNReal.ofReal (-f x)) Nᶜ = 0
    rw [withDensity_apply _ hN.compl]
    apply setLIntegral_eq_zero hN.compl
    intro x hx
    simp only [Pi.zero_apply]
    apply ENNReal.ofReal_eq_zero.mpr
    exact neg_nonpos.mpr (le_of_not_gt hx)
  have hmup_full : mup.real P = mup.real univ := by
    rw [measureReal_def, measureReal_def,
      measure_of_measure_compl_eq_zero hmup_compl]
  have hmun_full : mun.real N = mun.real univ := by
    rw [measureReal_def, measureReal_def,
      measure_of_measure_compl_eq_zero hmun_compl]
  have hAp_nonneg : 0 ≤ᵐ[mu.restrict Ap] f := by
    change ∀ᵐ x ∂mu.restrict Ap, 0 ≤ f x
    rw [ae_restrict_iff' hAp]
    exact Eventually.of_forall fun x hx ↦ by simpa [P] using hApP hx
  have hAn_nonneg : 0 ≤ᵐ[mu.restrict An] fun x ↦ -f x := by
    change ∀ᵐ x ∂mu.restrict An, 0 ≤ -f x
    rw [ae_restrict_iff' hAn]
    exact Eventually.of_forall fun x hx ↦ by
      have hxN : f x < 0 := by simpa [N] using hAnN hx
      exact neg_nonneg.mpr hxN.le
  have hApint : (∫ x in Ap, f x ∂mu) = mup.real Ap := by
    rw [integral_eq_lintegral_of_nonneg_ae hAp_nonneg
      hf.aestronglyMeasurable.restrict]
    simp only [measureReal_def, mup, withDensity_apply _ hAp]
  have hAnnegint : (∫ x in An, -f x ∂mu) = mun.real An := by
    rw [integral_eq_lintegral_of_nonneg_ae hAn_nonneg
      hf.neg.aestronglyMeasurable.restrict]
    simp only [measureReal_def, mun, withDensity_apply _ hAn]
  have hAnint : (∫ x in An, f x ∂mu) = -mun.real An := by
    rw [← hAnnegint, ← integral_neg]
    simp
  have htotal : (∫ x, f x ∂mu) = mup.real univ - mun.real univ := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
    simp only [measureReal_def, mup, mun, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  have hdisj : Disjoint Ap An := by
    rw [Set.disjoint_left]
    intro x hxp hxn
    have hp : 0 ≤ f x := by simpa [P] using hApP hxp
    have hn : f x < 0 := by simpa [N] using hAnN hxn
    exact (not_lt_of_ge hp) hn
  refine ⟨Ap ∪ An, hAp.union hAn, ?_⟩
  rw [setIntegral_union hdisj hAn hf.integrableOn hf.integrableOn,
    hApint, hAnint, hApmeasure, hAnmeasure, hmup_full, hmun_full, htotal]
  ring

/-- Exact scalar splitting for an arbitrary integrable representative.
@isnad1 id=ex.3h3v.s7.c55c14180f76 from=translated src=- shape=5469586a vocab=17353603
-/
theorem exists_setIntegral_eq_mul_real
    (mu : Measure ℝ) [NullSingletonClass mu]
    {f : ℝ → ℝ} (hf : Integrable f mu)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ A : Set ℝ, MeasurableSet A ∧
      (∫ x in A, f x ∂mu) = a * ∫ x, f x ∂mu := by
  let g : ℝ → ℝ := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[mu] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g mu := hf.congr hfg
  obtain ⟨A, hA, hEq⟩ := exists_setIntegral_eq_mul_real_of_measurable
    mu hg hf.aestronglyMeasurable.measurable_mk ha0 ha1
  refine ⟨A, hA, ?_⟩
  calc
    (∫ x in A, f x ∂mu) = ∫ x in A, g x ∂mu :=
      integral_congr_ae (ae_restrict_of_ae hfg)
    _ = a * ∫ x, g x ∂mu := hEq
    _ = a * ∫ x, f x ∂mu := by rw [integral_congr_ae hfg.symm]

/-! ## Lyapunov convexity from proportional splitting -/

/-- A reusable abstract implication: exact proportional splitting of every
integrable function implies convexity of every measurable set-integral
range.
@isnad1 id=haslyapu.1h3v.s7.e69cffc838e3 from=translated src=- shape=b5eb1e54 vocab=35ad0d54
-/
theorem hasLyapunovConvexity_of_proportional_splitting
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega)
    (hsplit : ∀ (f : Omega → E), Integrable f mu →
      ∀ {a : ℝ}, 0 ≤ a → a ≤ 1 →
        ∃ A : Set Omega, MeasurableSet A ∧
          (∫ x in A, f x ∂mu) = a • ∫ x, f x ∂mu) :
    HasLyapunovConvexity mu E := by
  intro f hf
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨A, hA, rfl⟩
  rcases hy with ⟨B, hB, rfl⟩
  let p : Omega → E := A.indicator f
  let q : Omega → E := B.indicator f
  have hp : Integrable p mu := hf.integrableOn.integrable_indicator hA
  have hq : Integrable q mu := hf.integrableOn.integrable_indicator hB
  have hpq : Integrable (fun w ↦ p w - q w) mu := hp.sub hq
  obtain ⟨D, hD, hsplitD⟩ := hsplit (fun w ↦ p w - q w) hpq ha (by linarith)
  let C : Set Omega := (D ∩ A) ∪ (Dᶜ ∩ B)
  have hC : MeasurableSet C := (hD.inter hA).union (hD.compl.inter hB)
  have hind : C.indicator f = fun w ↦ q w + D.indicator (fun z ↦ p z - q z) w := by
    funext w
    by_cases hwD : w ∈ D <;> by_cases hwA : w ∈ A <;> by_cases hwB : w ∈ B <;>
      simp [C, p, q, hwD, hwA, hwB]
  refine ⟨C, hC, ?_⟩
  rw [← integral_indicator hC, hind,
    integral_add hq (hpq.integrableOn.integrable_indicator hD),
    integral_indicator hD, hsplitD, integral_sub hp hq,
    integral_indicator hA, integral_indicator hB]
  have hb' : b = 1 - a := by linarith
  rw [hb']
  module

/-- Exact scalar Lyapunov convexity on the real Borel line.  Finiteness of
the base measure is unnecessary because integrability makes the positive and
negative density measures finite.
@isnad1 id=haslyapu.0h1v.s4.44e2b7ca782d from=translated src=- shape=d4c7d840 vocab=58d3db02
-/
theorem hasLyapunovConvexity_real_of_nullSingletonClass
    (mu : Measure ℝ) [NullSingletonClass mu] :
    HasLyapunovConvexity mu ℝ := by
  apply hasLyapunovConvexity_of_proportional_splitting mu
  intro f hf a ha0 ha1
  obtain ⟨A, hA, hEq⟩ := exists_setIntegral_eq_mul_real mu hf ha0 ha1
  exact ⟨A, hA, by simpa [smul_eq_mul] using hEq⟩

/-! ## Exact vector splitting for simple functions -/

namespace SimpleFunc

/-- A vector-valued simple function over a finite real atomless measure can
be split exactly in any prescribed proportion.  This is the simple-function
core of the finite-dimensional Lyapunov theorem.
@isnad1 id=ex.2h4v.s7.514716e6a82f from=translated src=- shape=97af9b16 vocab=b9298a42
-/
theorem exists_setIntegral_eq_smul_of_nullSingletonClass
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (f : SimpleFunc ℝ E) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ A : Set ℝ, MeasurableSet A ∧
      (∫ x in A, f x ∂mu) = a • ∫ x, f x ∂mu := by
  classical
  have hfiber : ∀ y : E, MeasurableSet (f ⁻¹' {y}) := fun y ↦
    f.measurableSet_fiber y
  have hexists : ∀ y : E, ∃ A : Set ℝ,
      A ⊆ f ⁻¹' {y} ∧ MeasurableSet A ∧
        mu.real A = a * mu.real (f ⁻¹' {y}) := fun y ↦
    exists_measurable_subset_measureReal_eq_mul mu (hfiber y) ha0 ha1
  choose As hAs hAsmeas hAsmeasure using hexists
  let A : Set ℝ := ⋃ y ∈ f.range, As y
  have hA : MeasurableSet A := by
    exact Finset.measurableSet_biUnion f.range fun y _ ↦ hAsmeas y
  have hinter : ∀ y ∈ f.range, f ⁻¹' {y} ∩ A = As y := by
    intro y hy
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx.2 with ⟨z, hxz⟩
      rcases Set.mem_iUnion.mp hxz with ⟨hz, hxAs⟩
      have hfxz : f x = z := hAs z hxAs
      have hfxy : f x = y := hx.1
      have hzy : z = y := hfxz.symm.trans hfxy
      simpa [hzy] using hxAs
    · intro x hx
      refine ⟨hAs y hx, ?_⟩
      exact Set.mem_iUnion_of_mem y (Set.mem_iUnion_of_mem hy hx)
  refine ⟨A, hA, ?_⟩
  rw [f.integral_eq_sum f.integrable_of_isFiniteMeasure.integrableOn,
    f.integral_eq_sum f.integrable_of_isFiniteMeasure]
  simp_rw [measureReal_restrict_apply (hfiber _)]
  have hsum :
      ∑ y ∈ f.range, mu.real (f ⁻¹' {y} ∩ A) • y =
        ∑ y ∈ f.range, (a * mu.real (f ⁻¹' {y})) • y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [hinter y hy, hAsmeasure y]
  rw [hsum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [smul_smul]

end SimpleFunc

/-! ## Transport under measurable equivalences -/

/-- The measurable set-integral range is invariant under a measurable
change of coordinates on the base space.
@isnad1 id=eq.0h6v.s6.732db22dc150 from=translated src=- shape=6b72bcff vocab=37d73b9c
-/
theorem measurableSetIntegralRange_map_measurableEquiv
    {Omega Omega' E : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) (e : Omega ≃ᵐ Omega') (f : Omega → E) :
    measurableSetIntegralRange (Measure.map e mu)
        (fun y ↦ f (e.symm y)) =
      measurableSetIntegralRange mu f := by
  have hIntegral : ∀ (B : Set Omega'), MeasurableSet B →
      (∫ y in B, f (e.symm y) ∂(Measure.map e mu)) =
        ∫ x in e ⁻¹' B, f x ∂mu := by
    intro B hB
    rw [e.restrict_map, integral_map_equiv]
    simp
  ext z
  constructor
  · rintro ⟨B, hB, hz⟩
    refine ⟨e ⁻¹' B, e.measurable hB, ?_⟩
    rw [← hIntegral B hB]
    exact hz
  · rintro ⟨A, hA, hz⟩
    refine ⟨e '' A, (e.measurableSet_image).2 hA, ?_⟩
    rw [hIntegral (e '' A) ((e.measurableSet_image).2 hA)]
    simpa using hz

/-- Lyapunov convexity is invariant under measurable equivalences of the
base space.
@isnad1 id=iff.0h5v.s6.5c6c116cb16e from=translated src=- shape=018becd3 vocab=0be43063
-/
theorem hasLyapunovConvexity_map_measurableEquiv_iff
    {Omega Omega' E : Type*} [MeasurableSpace Omega] [MeasurableSpace Omega']
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) (e : Omega ≃ᵐ Omega') :
    HasLyapunovConvexity (Measure.map e mu) E ↔
      HasLyapunovConvexity mu E := by
  constructor
  · intro h f hf
    let g : Omega' → E := fun y ↦ f (e.symm y)
    have hg : Integrable g (Measure.map e mu) := by
      rw [integrable_map_equiv e]
      refine hf.congr (Eventually.of_forall fun x ↦ ?_)
      simp only [g, Function.comp_apply]
      rw [e.symm_apply_apply]
    have hconv := h g hg
    rw [measurableSetIntegralRange_map_measurableEquiv mu e f] at hconv
    exact hconv
  · intro h f hf
    let g : Omega → E := fun x ↦ f (e x)
    have hg : Integrable g mu := by
      exact (integrable_map_equiv e f).mp hf
    have hconv := h g hg
    have hrange := measurableSetIntegralRange_map_measurableEquiv mu e g
    have hgeq : (fun y ↦ g (e.symm y)) = f := by
      funext y
      simp [g]
    rw [hgeq] at hrange
    rw [hrange]
    exact hconv

/-- Scalar Lyapunov convexity on any measurable space measurably equivalent
to the real line, provided the transported measure has no point masses.
@isnad1 id=haslyapu.0h3v.s6.6c7769b51bf9 from=translated src=- shape=50ec1501 vocab=6a8dbc56
-/
theorem hasLyapunovConvexity_real_of_measurableEquiv
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (e : Omega ≃ᵐ ℝ)
    [NullSingletonClass (Measure.map e mu)] :
    HasLyapunovConvexity mu ℝ := by
  exact (hasLyapunovConvexity_map_measurableEquiv_iff mu e).mp
    (hasLyapunovConvexity_real_of_nullSingletonClass (Measure.map e mu))

/-- A genuine atomless measure on a space measurably equivalent to `ℝ`
satisfies scalar Lyapunov convexity.
@isnad1 id=haslyapu.1h3v.s5.ed6e5cf7dffd from=translated src=- shape=161fbb35 vocab=6e73fa8d
-/
theorem hasLyapunovConvexity_real_of_atomless_measurableEquiv
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (hmu : IsAtomlessMeasure mu)
    (e : Omega ≃ᵐ ℝ) :
    HasLyapunovConvexity mu ℝ := by
  letI : MeasurableSingletonClass Omega :=
    ⟨fun x ↦ by
      have heq : ({x} : Set Omega) = e ⁻¹' {e x} := by
        ext y
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h ↦ by simpa [h], fun h ↦ e.injective h⟩
      rw [heq]
      exact e.measurable (measurableSet_singleton (e x))⟩
  letI : NullSingletonClass mu := hmu.toNullSingletonClass
  letI : NullSingletonClass (Measure.map e mu) :=
    ⟨fun y ↦ by
      rw [Measure.map_apply_of_aemeasurable e.measurable.aemeasurable
        (measurableSet_singleton y)]
      have heq : e ⁻¹' ({y} : Set ℝ) = {e.symm y} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h ↦ e.injective (h.trans (e.apply_symm_apply y).symm),
          fun h ↦ by simpa [h]⟩
      rw [heq, measure_singleton]⟩
  exact hasLyapunovConvexity_real_of_measurableEquiv mu e

end RandomSetTheory
