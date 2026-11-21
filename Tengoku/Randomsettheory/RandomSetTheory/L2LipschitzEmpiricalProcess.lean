/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.BoundedVarianceBernstein
import Tengoku.Randomsettheory.RandomSetTheory.MixedSupportChaining

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Truncated empirical processes with an `L²` Lipschitz envelope

This file develops the probabilistic core of the pointwise random-set CLT in
a form independent of random sets.  An observation `z` contributes a
continuous process `H z`.  Its increments are dominated by a nonnegative
random Lipschitz envelope `R z`.  After truncation at a deterministic level
`M`, the centered empirical increments have a Bernstein certificate whose
variance term depends on `E R²`, while its linear term depends on `M`.

For the Lindeberg choice `M = a * sqrt n`, normalization by `sqrt n` therefore
leaves both Bernstein metrics bounded uniformly in the sample size.  This is
the key estimate needed before Euclidean chaining and tightness.
-/

open Filter Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Ω Z T ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  [PseudoMetricSpace T] {μ : Measure Ω}

/-- Package a real together with a proof of nonnegativity as an `NNReal`.
Using this named constructor keeps typeclass inference stable inside products
of Bernstein proxies.-/
def nnrealOfNonneg (x : ℝ) (hx : 0 ≤ x) : ℝ≥0 := ⟨x, hx⟩

/--
@isnad1 id=eq.1h1v.s4.b6a83cf3a8b3 from=translated src=- shape=5dd5ca4f vocab=48fe800c
-/
@[simp]
theorem coe_nnrealOfNonneg (x : ℝ) (hx : 0 ≤ x) :
    (nnrealOfNonneg x hx : ℝ) = x := rfl

/-- Truncate a process-valued observation to zero when its Lipschitz envelope
exceeds `M`.  The truncation decision is independent of the index `t`, so
continuity and homogeneity in `t` are preserved.-/
def truncatedLipschitzObservation
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ) (z : Z) (t : T) : ℝ :=
  if R z ≤ M then H z t else 0

/-- The increment of one truncated observation.-/
def truncatedLipschitzIncrement
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (X : ι → Ω → Z) (i : ι) (s t : T) (ω : Ω) : ℝ :=
  truncatedLipschitzObservation H R M (X i ω) s -
    truncatedLipschitzObservation H R M (X i ω) t

/-- A centered, normalized finite empirical process.-/
def centeredTruncatedEmpiricalProcess
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : ι → Ω → Z) (I : Finset ι) (ω : Ω) (t : T) : ℝ :=
  c * ∑ i ∈ I,
    (truncatedLipschitzObservation H R M (X i ω) t -
      ∫ ξ, truncatedLipschitzObservation H R M (X i ξ) t ∂μ)

/--
@isnad1 id=measurab.2h6v.s5.eac0ea544b83 from=translated src=- shape=c2cc1399 vocab=7f21284e
-/
theorem measurable_truncatedLipschitzObservation
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hR : Measurable R)
    (t : T) :
    Measurable (fun z ↦ truncatedLipschitzObservation H R M z t) := by
  unfold truncatedLipschitzObservation
  exact Measurable.ite (measurableSet_le hR measurable_const) (hH t) measurable_const

/--
@isnad1 id=measurab.3h11v.s6.7b89f09c2d13 from=translated src=- shape=12f68799 vocab=4c03259b
-/
theorem measurable_truncatedLipschitzIncrement
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (X : ι → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hR : Measurable R)
    (i : ι) (s t : T) :
    Measurable (truncatedLipschitzIncrement H R M X i s t) := by
  exact
    ((measurable_truncatedLipschitzObservation H R M hH hR s).comp (hX i)).sub
      ((measurable_truncatedLipschitzObservation H R M hH hR t).comp (hX i))

/-- Truncation preserves the Lipschitz estimate and replaces the random
coefficient by the deterministic level `M`.
@isnad1 id=le.3h8v.s7.855949d96f21 from=translated src=- shape=2d17d8c7 vocab=346f273c
-/
theorem abs_truncatedLipschitzObservation_sub_le
    (H : Z → T → ℝ) (R : Z → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (z : Z) (s t : T) :
    |truncatedLipschitzObservation H R M z s -
        truncatedLipschitzObservation H R M z t| ≤ M * dist s t := by
  by_cases hz : R z ≤ M
  · simp only [truncatedLipschitzObservation, ite_eq_left hz]
    exact (hLip z s t).trans
      (mul_le_mul_of_nonneg_right hz dist_nonneg)
  · simp only [truncatedLipschitzObservation, ite_eq_right hz, sub_zero, abs_zero]
    exact mul_nonneg hM dist_nonneg

/-- Before replacing the envelope by `M`, the truncated increment is still
dominated by the original random envelope.
@isnad1 id=le.2h8v.s7.331609a2570b from=translated src=- shape=ee8b52b6 vocab=346f273c
-/
theorem abs_truncatedLipschitzObservation_sub_le_envelope
    (H : Z → T → ℝ) (R : Z → ℝ) (M : ℝ)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (z : Z) (s t : T) :
    |truncatedLipschitzObservation H R M z s -
        truncatedLipschitzObservation H R M z t| ≤ R z * dist s t := by
  by_cases hz : R z ≤ M
  · simpa only [truncatedLipschitzObservation, ite_eq_left hz] using hLip z s t
  · simp only [truncatedLipschitzObservation, ite_eq_right hz, sub_zero, abs_zero]
    exact mul_nonneg (hR z) dist_nonneg

/-- Every truncated increment is integrable on a finite measure space; no
moment assumption is needed after truncation.
@isnad1 id=integrab.6h12v.s7.1ec943874386 from=translated src=- shape=99ac28a4 vocab=cb078623
-/
theorem integrable_truncatedLipschitzIncrement
    [IsFiniteMeasure μ]
    (H : Z → T → ℝ) (R : Z → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (X : ι → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (i : ι) (s t : T) :
    Integrable (truncatedLipschitzIncrement H R M X i s t) μ := by
  apply Integrable.of_bound
    (measurable_truncatedLipschitzIncrement
      H R M X hX hH hRmeas i s t).aestronglyMeasurable
    (M * dist s t)
  filter_upwards with ω
  simpa only [truncatedLipschitzIncrement, Real.norm_eq_abs] using
    abs_truncatedLipschitzObservation_sub_le
      H R hM hR hLip (X i ω) s t

/-- Algebraic increment identity for the centered finite empirical process.
@isnad1 id=eq.1h14v.s7.23d37de179ef from=translated src=- shape=a7082a22 vocab=60f25372
-/
theorem centeredTruncatedEmpiricalProcess_sub
    (H : Z → T → ℝ) (R : Z → ℝ) (M c : ℝ)
    (X : ι → Ω → Z) (I : Finset ι) (ω : Ω) (s t : T) :
    (∀ i ∈ I, ∀ u : T,
      Integrable (fun ξ ↦ truncatedLipschitzObservation H R M (X i ξ) u) μ) →
    centeredTruncatedEmpiricalProcess (μ := μ) H R M c X I ω s -
        centeredTruncatedEmpiricalProcess (μ := μ) H R M c X I ω t =
      c * ∑ i ∈ I,
        (truncatedLipschitzIncrement H R M X i s t ω -
          ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ) := by
  intro hint
  unfold centeredTruncatedEmpiricalProcess truncatedLipschitzIncrement
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_sub]
  · ring
  · exact hint i hi s
  · exact hint i hi t

/-- A single centered truncated increment has a Bernstein certificate.  Its
variance metric is controlled by the `L²` envelope and its scale metric by
the truncation level.
@isnad1 id=hasberns.9h13v.s8.7e4841a3f311 from=translated src=- shape=f56fc856 vocab=3f410dd1
-/
theorem hasBernsteinMGF_centered_truncatedLipschitzIncrement
    [IsProbabilityMeasure μ]
    (H : Z → T → ℝ) (R : Z → ℝ) {M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (X : ι → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (i : ι) (hRL2 : MemLp (fun ω ↦ R (X i ω)) 2 μ)
    (hRsecond : ∫ ω, R (X i ω) ^ 2 ∂μ ≤ K ^ 2)
    (s t : T) :
    HasBernsteinMGF
      (fun ω ↦ truncatedLipschitzIncrement H R M X i s t ω -
        ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ)
      ⟨2 * (K * dist s t) ^ 2, by positivity⟩
      ⟨2 * (M * dist s t), by positivity⟩ μ := by
  let W : Ω → ℝ := truncatedLipschitzIncrement H R M X i s t
  have hWmeas : Measurable W :=
    measurable_truncatedLipschitzIncrement H R M X hX hH hRmeas i s t
  have hWbound : ∀ ω, |W ω| ≤ M * dist s t := by
    intro ω
    exact abs_truncatedLipschitzObservation_sub_le H R hM hR hLip (X i ω) s t
  have hWL2 : MemLp W 2 μ :=
    MemLp.of_bound hWmeas.aestronglyMeasurable (M * dist s t)
      (Filter.Eventually.of_forall fun ω ↦ by
        simpa only [Real.norm_eq_abs] using hWbound ω)
  have hRsq : Integrable (fun ω ↦ R (X i ω) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hRL2.aestronglyMeasurable).1 hRL2
  have hright : Integrable (fun ω ↦ (R (X i ω) * dist s t) ^ 2) μ := by
    convert hRsq.const_mul (dist s t ^ 2) using 1
    ext ω
    ring
  have hWsq : Integrable (fun ω ↦ W ω ^ 2) μ :=
    (memLp_two_iff_integrable_sq hWL2.aestronglyMeasurable).1 hWL2
  have hWsecond : ∫ ω, W ω ^ 2 ∂μ ≤ (K * dist s t) ^ 2 := by
    calc
      ∫ ω, W ω ^ 2 ∂μ ≤
          ∫ ω, (R (X i ω) * dist s t) ^ 2 ∂μ := by
        apply integral_mono_ae hWsq hright
        filter_upwards with ω
        have henv :=
          abs_truncatedLipschitzObservation_sub_le_envelope
            H R M hR hLip (X i ω) s t
        exact sq_le_sq' (neg_le_of_abs_le henv) (le_of_abs_le henv)
      _ = dist s t ^ 2 * ∫ ω, R (X i ω) ^ 2 ∂μ := by
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
      _ ≤ dist s t ^ 2 * K ^ 2 :=
        mul_le_mul_of_nonneg_left hRsecond (sq_nonneg _)
      _ = (K * dist s t) ^ 2 := by ring
  exact hasBernsteinMGF_centered_of_memLp_two_of_ae_abs_le
    W hWL2 (sq_nonneg _) (mul_nonneg hM dist_nonneg)
      (Filter.Eventually.of_forall hWbound) hWsecond

/-- The normalized finite sum of independent truncated increments inherits
the mixed Bernstein metric.  This is stated before making any particular
choice of sample size or truncation level.
@isnad1 id=hasberns.10h14v.s9.d6948f434483 from=translated src=- shape=0c6eb6f1 vocab=b589b0a2
-/
theorem hasBernsteinMGF_centeredTruncatedEmpiricalProcess_increment
    [IsProbabilityMeasure μ]
    (H : Z → T → ℝ) (R : Z → ℝ) {M K : ℝ} (c : ℝ≥0)
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (X : ι → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (I : Finset ι)
    (hRL2 : ∀ i ∈ I, MemLp (fun ω ↦ R (X i ω)) 2 μ)
    (hRsecond : ∀ i ∈ I, ∫ ω, R (X i ω) ^ 2 ∂μ ≤ K ^ 2)
    (s t : T) :
    HasBernsteinMGF
      (fun ω ↦ (c : ℝ) * ∑ i ∈ I,
        (truncatedLipschitzIncrement H R M X i s t ω -
          ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ))
      (c ^ 2 *
        ∑ _i ∈ I, nnrealOfNonneg (2 * (K * dist s t) ^ 2) (by positivity))
      (c *
        nnrealOfNonneg (2 * (M * dist s t)) (by positivity)) μ := by
  let W : ι → Ω → ℝ := fun i ↦
    truncatedLipschitzIncrement H R M X i s t
  let m : ι → ℝ := fun i ↦ ∫ ξ, W i ξ ∂μ
  have hcenteredIndep : iIndepFun (fun i ω ↦ W i ω - m i) μ := by
    have hcomp := hIndep.comp
      (fun i z ↦
        (truncatedLipschitzObservation H R M z s -
          truncatedLipschitzObservation H R M z t) - m i)
      (fun i ↦
        ((measurable_truncatedLipschitzObservation H R M hH hRmeas s).sub
          (measurable_truncatedLipschitzObservation H R M hH hRmeas t)).sub
            measurable_const)
    convert hcomp using 1
    funext i ω
    rfl
  have hB : ∀ i ∈ I,
      HasBernsteinMGF (fun ω ↦ W i ω - m i)
        ⟨2 * (K * dist s t) ^ 2, by positivity⟩
        ⟨2 * (M * dist s t), by positivity⟩ μ := by
    intro i hi
    simpa only [W, m] using
      hasBernsteinMGF_centered_truncatedLipschitzIncrement
        H R hM hK X hX hH hRmeas hR hLip i (hRL2 i hi)
          (hRsecond i hi) s t
  have hsum := HasBernsteinMGF.sum_of_iIndepFun hcenteredIndep
    (nnrealOfNonneg (2 * (M * dist s t)) (by positivity))
    (v := fun _ ↦ nnrealOfNonneg (2 * (K * dist s t) ^ 2) (by positivity))
    (s := I) hB
  exact hsum.nnreal_mul c

/-- Confidence form of the increment estimate for a nonempty finite sample.
The threshold is left in terms of the two explicit `NNReal` proxies; later
specializations only need deterministic algebra to put it in mixed-metric
form.
@isnad1 id=other.14h15v.s9.e90b70da2716 from=translated src=- shape=89fb5a30 vocab=8714f978
-/
theorem measureReal_centeredTruncatedEmpiricalProcess_increment_le
    [IsProbabilityMeasure μ]
    (H : Z → T → ℝ) (R : Z → ℝ) {M K : ℝ} (c : ℝ≥0)
    (hM : 0 ≤ M) (hK : 0 < K) (hc : 0 < c)
    (X : ι → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (I : Finset ι) (hI : I.Nonempty)
    (hRL2 : ∀ i ∈ I, MemLp (fun ω ↦ R (X i ω)) 2 μ)
    (hRsecond : ∀ i ∈ I, ∫ ω, R (X i ω) ^ 2 ∂μ ≤ K ^ 2)
    (s t : T) (hdist : 0 < dist s t) {y : ℝ} (hy : 0 ≤ y) :
    let v : ℝ≥0 := c ^ 2 *
      ∑ _i ∈ I, nnrealOfNonneg (2 * (K * dist s t) ^ 2) (by positivity)
    let b : ℝ≥0 := c *
      nnrealOfNonneg (2 * (M * dist s t)) (by positivity)
    μ.real { ω |
      Real.sqrt (2 * (v : ℝ) * y) + 2 * (b : ℝ) * y ≤
        |(c : ℝ) * ∑ i ∈ I,
          (truncatedLipschitzIncrement H R M X i s t ω -
            ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ)| } ≤
      2 * Real.exp (-y) := by
  dsimp only
  have hmgf := hasBernsteinMGF_centeredTruncatedEmpiricalProcess_increment
    H R c hM hK.le X hX hIndep hH hRmeas hR hLip I hRL2 hRsecond s t
  apply hmgf.measure_abs_ge_sqrt_add_le hy
  push_cast
  simp only [coe_nnrealOfNonneg, Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (I.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hI)
  positivity

/-- With truncation level `a * sqrt (n+1)` and CLT normalization, the
increment bound is uniform in the sample size.  The two mixed metrics are
`2 K * dist` and `2 a * dist`; the deliberately loose factor in the Gaussian
metric avoids fragile square-root normalizations and is harmless for
chaining.
@isnad1 id=le.11h13v.s9.476ccda39ec3 from=translated src=- shape=7ef77e24 vocab=fe16b3d4
-/
theorem measureReal_range_succ_centeredTruncated_increment_mixedTail
    [IsProbabilityMeasure μ]
    (H : Z → T → ℝ) (R : Z → ℝ) {a K : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K)
    (X : ℕ → Ω → Z) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X μ)
    (hH : ∀ t, Measurable (fun z ↦ H z t)) (hRmeas : Measurable R)
    (hR : ∀ z, 0 ≤ R z)
    (hLip : ∀ z s t, |H z s - H z t| ≤ R z * dist s t)
    (hRL2 : ∀ i, MemLp (fun ω ↦ R (X i ω)) 2 μ)
    (hRsecond : ∀ i, ∫ ω, R (X i ω) ^ 2 ∂μ ≤ K ^ 2)
    (n : ℕ) (s t : T) (y : ℝ) (hy : 0 ≤ y) :
    μ.real { ω |
      (2 * K) * dist s t * Real.sqrt (2 * y) +
          2 * (2 * a) * dist s t * y <
        |(Real.sqrt (n + 1 : ℝ))⁻¹ * ∑ i ∈ Finset.range (n + 1),
          (truncatedLipschitzIncrement H R
              (a * Real.sqrt (n + 1 : ℝ)) X i s t ω -
            ∫ ξ, truncatedLipschitzIncrement H R
              (a * Real.sqrt (n + 1 : ℝ)) X i s t ξ ∂μ)| } ≤
      2 * Real.exp (-y) := by
  let q : ℝ := Real.sqrt (n + 1 : ℝ)
  let M : ℝ := a * q
  let c : ℝ≥0 := Real.toNNReal q⁻¹
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hq : 0 < q := by
    dsimp only [q]
    exact Real.sqrt_pos.2 hn
  have hM : 0 ≤ M := mul_nonneg ha hq.le
  have hc : 0 < c := by
    dsimp only [c]
    exact Real.toNNReal_pos.mpr (inv_pos.mpr hq)
  have hccoe : (c : ℝ) = q⁻¹ := by
    dsimp only [c]
    exact Real.coe_toNNReal _ (inv_nonneg.mpr hq.le)
  by_cases hdistzero : dist s t = 0
  · have hinczero : ∀ i ω,
        truncatedLipschitzIncrement H R M X i s t ω = 0 := by
      intro i ω
      have hb := abs_truncatedLipschitzObservation_sub_le
        H R hM hR hLip (X i ω) s t
      rw [hdistzero, mul_zero] at hb
      exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
    have hprocesszero : ∀ ω,
        q⁻¹ * ∑ i ∈ Finset.range (n + 1),
          (truncatedLipschitzIncrement H R M X i s t ω -
            ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ) = 0 := by
      intro ω
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro i hi
      rw [hinczero i ω]
      have hint : ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ = 0 := by
        simp_rw [hinczero i]
        simp
      rw [hint, sub_zero]
    have hset : { ω |
        (2 * K) * dist s t * Real.sqrt (2 * y) +
            2 * (2 * a) * dist s t * y <
          |q⁻¹ * ∑ i ∈ Finset.range (n + 1),
            (truncatedLipschitzIncrement H R M X i s t ω -
              ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ)| } =
        ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        hprocesszero, abs_zero, hdistzero, mul_zero, zero_mul, add_zero,
        lt_self_iff_false]
    change μ.real { ω |
        (2 * K) * dist s t * Real.sqrt (2 * y) +
            2 * (2 * a) * dist s t * y <
          |q⁻¹ * ∑ i ∈ Finset.range (n + 1),
            (truncatedLipschitzIncrement H R M X i s t ω -
              ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ)| } ≤ _
    rw [hset]
    simp only [measureReal_empty]
    exact mul_nonneg (by norm_num) (Real.exp_pos _).le
  · have hdist : 0 < dist s t := lt_of_le_of_ne dist_nonneg
        (Ne.symm hdistzero)
    have htail := measureReal_centeredTruncatedEmpiricalProcess_increment_le
      H R c hM hK hc X hX hIndep hH hRmeas hR hLip
        (Finset.range (n + 1)) (by simp) (fun i _ ↦ hRL2 i)
        (fun i _ ↦ hRsecond i) s t hdist hy
    dsimp only at htail
    have hv :
        (((c ^ 2 * ∑ _i ∈ Finset.range (n + 1),
          nnrealOfNonneg (2 * (K * dist s t) ^ 2) (by positivity)) : ℝ≥0) : ℝ) =
          2 * (K * dist s t) ^ 2 := by
      push_cast
      rw [hccoe]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range,
        coe_nnrealOfNonneg]
      push_cast
      dsimp only [q] at hq ⊢
      rw [inv_pow, Real.sq_sqrt hn.le]
      field_simp
    have hb :
        (((c * nnrealOfNonneg (2 * (M * dist s t)) (by positivity)) : ℝ≥0) : ℝ) =
          2 * a * dist s t := by
      push_cast
      rw [hccoe]
      simp only [coe_nnrealOfNonneg, M]
      field_simp
    rw [hv, hb, hccoe] at htail
    have hsqrt :
        Real.sqrt (2 * (2 * (K * dist s t) ^ 2) * y) ≤
          (2 * K) * dist s t * Real.sqrt (2 * y) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have h2y : 0 ≤ 2 * y := by positivity
        nlinarith [Real.sq_sqrt h2y, sq_nonneg (K * dist s t)]
    apply (measureReal_mono ?_).trans htail
    intro ω hω
    change (2 * K) * dist s t * Real.sqrt (2 * y) +
        2 * (2 * a) * dist s t * y <
      |q⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (truncatedLipschitzIncrement H R M X i s t ω -
          ∫ ξ, truncatedLipschitzIncrement H R M X i s t ξ ∂μ)| at hω
    have hlinear : 2 * (2 * a * dist s t) * y =
        2 * (2 * a) * dist s t * y := by ring
    exact (add_le_add hsqrt hlinear.le).trans hω.le

end ProbabilityTheory
