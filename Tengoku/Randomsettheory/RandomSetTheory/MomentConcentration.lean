/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanNetCardinality
import Tengoku.Seed.Probability.Moments.Variance
import Tengoku.Seed.Algebra.Order.Chebyshev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial moment and Chebyshev concentration for random sets

This file complements the exponential Hoeffding, sub-Gaussian, and Bernstein
bounds with estimates available under finite-moment assumptions.

The scalar layer contains:

* Markov's inequality for the absolute moment `E |X|^q`;
* the deterministic inequality
  `|sum X_i|^q ≤ card^(q-1) * sum |X_i|^q` for positive integer `q`;
* its consequence for finite averages, without independence or centering;
* the sharper Chebyshev bound for independent centered `L²` variables,
  using exact additivity of variance.

The random-set layer transfers both families of directional bounds from
support functions to Hausdorff distance, first over an arbitrary finite net
and then with the volumetric factor `(1 + 2 / eps)^finrank`.

## Deliberate limitation

The order-`q` result is a one-scale Markov plus union-bound estimate.  It does
**not** formalize the Fuk--Nagaev/symmetrization/chaining argument needed for
the sharper mixed Gaussian-polynomial rate in the report.  In particular,
the crude moment-of-average estimate need not decay with sample size.  The
order-two specialization does recover the classical `1 / n` Chebyshev scale
under independence and centering.
-/

open Real Set Metric Finset MeasureTheory
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Absolute moment, defined with `|X|^q` so that odd orders are nonnegative.-/
def absoluteMoment (X : Ω → ℝ) (q : ℕ) (μ : Measure Ω) : ℝ :=
  ∫ ω, |X ω| ^ q ∂μ

/-- Absolute moments depend only on the law of a real random variable.
@isnad1 id=eq.1h7v.s5.b25964b1f848 from=translated src=- shape=17bbd797 vocab=57a87a86
-/
theorem IdentDistrib.absoluteMoment_eq
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (h : IdentDistrib X Y μ ν) (q : ℕ) :
    absoluteMoment X q μ = absoluteMoment Y q ν := by
  unfold absoluteMoment
  simpa only [Real.norm_eq_abs] using h.norm.pow.integral_eq

/--
@isnad1 id=le.0h4v.s4.d9101f40971a from=translated src=- shape=813e58f6 vocab=d83ea033
-/
theorem absoluteMoment_nonneg (X : Ω → ℝ) (q : ℕ) (μ : Measure Ω) :
    0 ≤ absoluteMoment X q μ :=
  integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _

/--
@isnad1 id=le.2h5v.s7.5a10d6366ac1 from=translated src=- shape=b50dbec1 vocab=bc8fdf87
-/
theorem measureReal_abs_ge_le_absoluteMoment_div
    [IsFiniteMeasure μ] (X : Ω → ℝ) (q : ℕ)
    (hX : Integrable (fun ω => |X ω| ^ q) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ absoluteMoment X q μ / t ^ q := by
  let f : Ω → ℝ := fun ω => |X ω| ^ q / t ^ q
  have htq : 0 < t ^ q := pow_pos ht q
  have hfint : Integrable f μ := hX.div_const _
  have hfnn : 0 ≤ᵐ[μ] f := ae_of_all μ fun ω =>
    div_nonneg (pow_nonneg (abs_nonneg _) _) htq.le
  have hs : ∀ ω ∈ {ω | t ≤ |X ω|}, 1 ≤ f ω := by
    intro ω hω
    change 1 ≤ |X ω| ^ q / t ^ q
    rw [le_div_iff₀ htq]
    simpa using pow_le_pow_left₀ ht.le hω q
  have hmarkov : μ {ω | t ≤ |X ω|} ≤
      ENNReal.ofReal (∫ ω, f ω ∂μ) :=
    hfint.measure_le_integral hfnn hs
  have htop : μ {ω | t ≤ |X ω|} ≠ ∞ := measure_ne_top μ _
  have hreal := ENNReal.toReal_le_toReal htop (by finiteness) |>.2 hmarkov
  have hmomentnn : 0 ≤ absoluteMoment X q μ := absoluteMoment_nonneg X q μ
  have hrhs : 0 ≤ absoluteMoment X q μ / t ^ q :=
    div_nonneg hmomentnn htq.le
  have hintf : (∫ ω, f ω ∂μ) = absoluteMoment X q μ / t ^ q := by
    simp only [f, absoluteMoment, integral_div]
  rw [hintf, ENNReal.toReal_ofReal hrhs] at hreal
  exact hreal

/--
@isnad1 id=le.3h6v.s7.1b0b5d7409a8 from=translated src=- shape=bf2fe85f vocab=bc8fdf87
-/
theorem measureReal_abs_ge_le_of_absoluteMoment_le
    [IsFiniteMeasure μ] (X : Ω → ℝ) {q : ℕ}
    (hX : Integrable (fun ω => |X ω| ^ q) μ)
    {M t : ℝ} (hM : absoluteMoment X q μ ≤ M) (ht : 0 < t) :
    μ.real {ω | t ≤ |X ω|} ≤ M / t ^ q := by
  exact (measureReal_abs_ge_le_absoluteMoment_div X q hX ht).trans
    (div_le_div_of_nonneg_right hM (pow_nonneg ht.le q))

/--
@isnad1 id=le.1h4v.s6.847504351752 from=translated src=- shape=cadc4419 vocab=2f41bd11
-/
theorem abs_finset_sum_pow_le
    (x : ι → ℝ) (s : Finset ι) {q : ℕ} (hq : 0 < q) :
    |∑ i ∈ s, x i| ^ q ≤
      (s.card : ℝ) ^ (q - 1) * ∑ i ∈ s, |x i| ^ q := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  calc
    |∑ i ∈ s, x i| ^ (n + 1) ≤ (∑ i ∈ s, |x i|) ^ (n + 1) := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ (s.card : ℝ) ^ n * ∑ i ∈ s, |x i| ^ (n + 1) := by
      exact pow_sum_le_card_mul_sum_pow (s := s) (f := fun i => |x i|)
        (fun _ _ => abs_nonneg _) n
    _ = (s.card : ℝ) ^ ((n + 1) - 1) *
        ∑ i ∈ s, |x i| ^ (n + 1) := by simp

/--
@isnad1 id=integrab.3h6v.s7.1e4039a95cc5 from=translated src=- shape=0104130a vocab=1335d708
-/
theorem integrable_abs_finset_sum_pow
    (X : ι → Ω → ℝ) (s : Finset ι) {q : ℕ} (hq : 0 < q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXq : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ q) μ) :
    Integrable (fun ω => |∑ i ∈ s, X i ω| ^ q) μ := by
  let g : Ω → ℝ := fun ω => ∑ i ∈ s, |X i ω| ^ q
  have hgint : Integrable g μ := by
    exact integrable_finsetSum s fun i hi => hXq i hi
  have hmajorant : Integrable (fun ω => (s.card : ℝ) ^ (q - 1) * g ω) μ :=
    hgint.const_mul _
  have hsumMeas : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) μ :=
    Finset.aemeasurable_fun_sum s hX
  apply Integrable.mono' hmajorant (hsumMeas.abs.pow_const q).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact abs_finset_sum_pow_le (fun i => X i ω) s hq

/--
@isnad1 id=le.3h6v.s7.222c31ccd13b from=translated src=- shape=85351bac vocab=6698f8fb
-/
theorem absoluteMoment_finset_sum_le
    (X : ι → Ω → ℝ) (s : Finset ι) {q : ℕ} (hq : 0 < q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXq : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ q) μ) :
    absoluteMoment (fun ω => ∑ i ∈ s, X i ω) q μ ≤
      (s.card : ℝ) ^ (q - 1) * ∑ i ∈ s, absoluteMoment (X i) q μ := by
  let g : Ω → ℝ := fun ω => ∑ i ∈ s, |X i ω| ^ q
  have hgint : Integrable g μ := by
    exact integrable_finsetSum s fun i hi => hXq i hi
  have hmajorant : Integrable (fun ω => (s.card : ℝ) ^ (q - 1) * g ω) μ :=
    hgint.const_mul _
  have htarget : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ q) μ :=
    integrable_abs_finset_sum_pow X s hq hX hXq
  unfold absoluteMoment
  calc
    (∫ ω, |∑ i ∈ s, X i ω| ^ q ∂μ) ≤
        ∫ ω, (s.card : ℝ) ^ (q - 1) * g ω ∂μ := by
      apply integral_mono htarget hmajorant
      intro ω
      exact abs_finset_sum_pow_le (fun i => X i ω) s hq
    _ = (s.card : ℝ) ^ (q - 1) *
        ∑ i ∈ s, ∫ ω, |X i ω| ^ q ∂μ := by
      rw [integral_const_mul]
      congr 1
      exact integral_finsetSum s hXq

/--
@isnad1 id=le.4h6v.s7.420ed276e5b7 from=translated src=- shape=ad3e1d8b vocab=3cfde867
-/
theorem absoluteMoment_finset_average_le
    (X : ι → Ω → ℝ) (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXq : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ q) μ) :
    absoluteMoment (fun ω => (∑ i ∈ s, X i ω) / (s.card : ℝ)) q μ ≤
      (∑ i ∈ s, absoluteMoment (X i) q μ) / (s.card : ℝ) := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsum := absoluteMoment_finset_sum_le X s hq hX hXq
  have havg :
      absoluteMoment (fun ω => (∑ i ∈ s, X i ω) / (s.card : ℝ)) q μ =
        absoluteMoment (fun ω => ∑ i ∈ s, X i ω) q μ / (s.card : ℝ) ^ q := by
    unfold absoluteMoment
    simp only [abs_div, abs_of_pos hcard, div_pow, integral_div]
  rw [havg]
  calc
    absoluteMoment (fun ω => ∑ i ∈ s, X i ω) q μ / (s.card : ℝ) ^ q ≤
        ((s.card : ℝ) ^ (q - 1) *
          ∑ i ∈ s, absoluteMoment (X i) q μ) / (s.card : ℝ) ^ q :=
      div_le_div_of_nonneg_right hsum (pow_nonneg hcard.le q)
    _ = (∑ i ∈ s, absoluteMoment (X i) q μ) / (s.card : ℝ) := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      simp only [Nat.succ_sub_one, pow_succ]
      field_simp

/--
@isnad1 id=le.5h7v.s7.06f5b5646dab from=translated src=- shape=f182ac97 vocab=757989fb
-/
theorem markov_finset_average_abs_real
    [IsFiniteMeasure μ]
    (X : ι → Ω → ℝ) (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXq : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ q) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      (∑ i ∈ s, absoluteMoment (X i) q μ) /
        ((s.card : ℝ) * t ^ q) := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsumInt := integrable_abs_finset_sum_pow X s hq hX hXq
  have hsumMoment := absoluteMoment_finset_sum_le X s hq hX hXq
  have htail := measureReal_abs_ge_le_absoluteMoment_div
    (μ := μ) (fun ω => ∑ i ∈ s, X i ω) q hsumInt (mul_pos hcard ht)
  have hset :
      {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} =
        {ω | (s.card : ℝ) * t ≤ |∑ i ∈ s, X i ω|} := by
    ext ω
    simp only [mem_ofPred_eq, abs_div, abs_of_pos hcard]
    rw [le_div_iff₀ hcard]
    simp only [mul_comm]
  rw [hset]
  calc
    μ.real {ω | (s.card : ℝ) * t ≤ |∑ i ∈ s, X i ω|} ≤
        absoluteMoment (fun ω => ∑ i ∈ s, X i ω) q μ /
          ((s.card : ℝ) * t) ^ q := htail
    _ ≤ ((s.card : ℝ) ^ (q - 1) *
          ∑ i ∈ s, absoluteMoment (X i) q μ) /
          ((s.card : ℝ) * t) ^ q :=
      div_le_div_of_nonneg_right hsumMoment
        (pow_nonneg (mul_nonneg hcard.le ht.le) q)
    _ = (∑ i ∈ s, absoluteMoment (X i) q μ) /
          ((s.card : ℝ) * t ^ q) := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      simp only [Nat.succ_sub_one, mul_pow, pow_succ]
      field_simp

/-- Common-moment specialization of `markov_finset_average_abs_real`.
It exposes the standard polynomial tail `M / t^q`.  No sample-size decay is
claimed, since no independence or centering is assumed.
@isnad1 id=le.6h8v.s7.672885f9f543 from=translated src=- shape=71367cd3 vocab=275dcfb4
-/
theorem markov_finset_average_abs_real_of_common_bound
    [IsFiniteMeasure μ]
    (X : ι → Ω → ℝ) (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXq : ∀ i ∈ s, Integrable (fun ω => |X i ω| ^ q) μ)
    {M t : ℝ}
    (hM : ∀ i ∈ s, absoluteMoment (X i) q μ ≤ M)
    (ht : 0 < t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤ M / t ^ q := by
  have h := markov_finset_average_abs_real X s hs hq hX hXq ht
  calc
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
        (∑ i ∈ s, absoluteMoment (X i) q μ) /
          ((s.card : ℝ) * t ^ q) := h
    _ ≤ ((s.card : ℝ) * M) / ((s.card : ℝ) * t ^ q) := by
      apply div_le_div_of_nonneg_right
      · simpa only [← nsmul_eq_mul, ← Finset.sum_const] using
          (Finset.sum_le_sum fun i hi => hM i hi)
      · positivity
    _ = M / t ^ q := by
      have hcard : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hs)
      field_simp

/-! ## A finite maximum under a common polynomial-moment bound -/

/-- Union bound for the upper tail of a finite family with a common absolute
moment bound.  Independence is not required.

If `E |Xᵢ|^q ≤ K^q`, then
`P(∃ i ∈ s, t < Xᵢ) ≤ |s| K^q / t^q`.
@isnad1 id=le.3h8v.s7.1628f1d25b8c from=translated src=- shape=2e45dfe8 vocab=09e0743d
-/
theorem measureReal_exists_gt_le_card_mul_pow_div
    [IsFiniteMeasure μ]
    (X : ι → Ω → ℝ) (s : Finset ι) {q : ℕ}
    (hXq : ∀ i ∈ s, Integrable (fun ω ↦ |X i ω| ^ q) μ)
    {K t : ℝ} (hK : ∀ i ∈ s, absoluteMoment (X i) q μ ≤ K ^ q)
    (ht : 0 < t) :
    μ.real {ω | ∃ i ∈ s, t < X i ω} ≤
      s.card * (K ^ q / t ^ q) := by
  have hset : {ω | ∃ i ∈ s, t < X i ω} =
      ⋃ i ∈ s, {ω | t < X i ω} := by
    ext ω
    simp
  rw [hset]
  calc
    μ.real (⋃ i ∈ s, {ω | t < X i ω}) ≤
        ∑ i ∈ s, μ.real {ω | t < X i ω} :=
      measureReal_biUnion_finset_le s _
    _ ≤ ∑ _i ∈ s, K ^ q / t ^ q := by
      apply Finset.sum_le_sum
      intro i hi
      have hsubset : {ω | t < X i ω} ⊆ {ω | t ≤ |X i ω|} := by
        intro ω hω
        exact hω.le.trans (le_abs_self (X i ω))
      exact (measureReal_mono hsubset (by finiteness)).trans
        (measureReal_abs_ge_le_of_absoluteMoment_le
          (X i) (hXq i hi) (hK i hi) ht)
    _ = s.card * (K ^ q / t ^ q) := by simp

/-- High-probability finite-maximum bound obtained by Markov's inequality
and a union bound.  If `s` is nonempty, `q > 0`, `K > 0`, and
`E |Xᵢ|^q ≤ K^q`, then with probability at least `1 - δ`,

`Xᵢ ≤ K * (|s| / δ)^(1/q)` for every `i ∈ s`.

The power in the threshold is `Real.rpow`; neither independence nor
centering is assumed.
@isnad1 id=le.7h8v.s8.a60f1be10981 from=translated src=- shape=d836d852 vocab=9f0dbf2e
-/
theorem one_sub_le_measureReal_forall_le_mul_card_div_rpow
    [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXq : ∀ i ∈ s, Integrable (fun ω ↦ |X i ω| ^ q) μ)
    {K δ : ℝ} (hKpos : 0 < K)
    (hK : ∀ i ∈ s, absoluteMoment (X i) q μ ≤ K ^ q)
    (hδ : 0 < δ) :
    1 - δ ≤ μ.real {ω | ∀ i ∈ s,
      X i ω ≤ K * ((s.card : ℝ) / δ) ^ (1 / (q : ℝ))} := by
  let r : ℝ := (s.card : ℝ) / δ
  let t : ℝ := K * r ^ (1 / (q : ℝ))
  let B : Set Ω := {ω | ∃ i ∈ s, t < X i ω}
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast s.card_pos.mpr hs
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : 0 < r := div_pos hcard hδ
  have ht : 0 < t := mul_pos hKpos (Real.rpow_pos_of_pos hr _)
  have hroot_pow : (r ^ (1 / (q : ℝ))) ^ q = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    rw [one_div, inv_mul_cancel₀ hqreal.ne', Real.rpow_one]
  have ht_pow : t ^ q = K ^ q * r := by
    simp only [t, mul_pow, hroot_pow]
  have hbad : μ.real B ≤ δ := by
    have htail := measureReal_exists_gt_le_card_mul_pow_div
      X s hXq hK ht
    calc
      μ.real B ≤ s.card * (K ^ q / t ^ q) := by
        simpa only [B] using htail
      _ = δ := by
        rw [ht_pow]
        have hKpow : K ^ q ≠ 0 := pow_ne_zero q hKpos.ne'
        dsimp only [r]
        field_simp
  have hBnull : NullMeasurableSet B μ := by
    have hunion : B = ⋃ i ∈ s, {ω | t < X i ω} := by
      ext ω
      simp [B]
    rw [hunion]
    apply s.nullMeasurableSet_biUnion
    intro i hi
    exact (hX i hi).nullMeasurableSet_preimage measurableSet_Ioi
  have hsum := measureReal_add_measureReal_compl₀ hBnull
  have hcompl : Bᶜ = {ω | ∀ i ∈ s, X i ω ≤ t} := by
    ext ω
    simp [B, not_lt]
  rw [probReal_univ, hcompl] at hsum
  dsimp only [t, r] at hsum ⊢
  linarith

/-- Chebyshev's inequality for a centered finite average.  Unlike the
general moment bound above, independence makes the variance additive and
therefore gives the classical `1 / card` scale for a common variance.
@isnad1 id=le.5h6v.s8.80c6c798a6c1 from=translated src=- shape=a8a31785 vocab=cdfc3821
-/
theorem chebyshev_finset_average_abs_real
    [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hcentered : ∀ i ∈ s, μ[X i] = 0)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      (∑ i ∈ s, variance (X i) μ) / (((s.card : ℝ) * t) ^ 2) := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hsumLp : MemLp (fun ω => ∑ i ∈ s, X i ω) 2 μ :=
    memLp_finsetSum s hX
  have hsumCentered : μ[fun ω => ∑ i ∈ s, X i ω] = 0 := by
    rw [integral_finsetSum s fun i hi => (hX i hi).integrable one_le_two]
    exact Finset.sum_eq_zero fun i hi => hcentered i hi
  have hpairwise : Set.Pairwise (s : Set ι) fun i j => X i ⟂ᵢ[μ] X j := by
    intro i hi j hj hij
    exact h_indep.indepFun hij
  have hvariance :
      variance (fun ω => ∑ i ∈ s, X i ω) μ =
        ∑ i ∈ s, variance (X i) μ :=
    by
      have hfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
        funext ω
        simp
      rw [hfun]
      exact IndepFun.variance_sum hX hpairwise
  have hENN := meas_ge_le_variance_div_sq hsumLp (mul_pos hcard ht)
  have hENN' :
      μ {ω | (s.card : ℝ) * t ≤ |∑ i ∈ s, X i ω|} ≤
        ENNReal.ofReal
          ((∑ i ∈ s, variance (X i) μ) / (((s.card : ℝ) * t) ^ 2)) := by
    simpa only [hsumCentered, sub_zero, hvariance] using hENN
  have hreal := (ENNReal.toReal_le_toReal (measure_ne_top μ _) (by finiteness)).2 hENN'
  have hrhs : 0 ≤
      (∑ i ∈ s, variance (X i) μ) / (((s.card : ℝ) * t) ^ 2) :=
    div_nonneg (Finset.sum_nonneg fun i _ => variance_nonneg (X i) μ) (sq_nonneg _)
  rw [ENNReal.toReal_ofReal hrhs] at hreal
  have hset :
      {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} =
        {ω | (s.card : ℝ) * t ≤ |∑ i ∈ s, X i ω|} := by
    ext ω
    simp only [mem_ofPred_eq, abs_div, abs_of_pos hcard]
    rw [le_div_iff₀ hcard]
    simp only [mul_comm]
  rw [hset]
  exact hreal

/-- Common-variance form of Chebyshev's inequality for a centered independent
finite average.
@isnad1 id=le.6h7v.s8.cfb154c26740 from=translated src=- shape=046aef58 vocab=cdfc3821
-/
theorem chebyshev_finset_average_abs_real_of_variance_le
    [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hcentered : ∀ i ∈ s, μ[X i] = 0)
    {V t : ℝ} (hvariance : ∀ i ∈ s, variance (X i) μ ≤ V)
    (ht : 0 < t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      V / ((s.card : ℝ) * t ^ 2) := by
  have h := chebyshev_finset_average_abs_real X h_indep s hs hX hcentered ht
  calc
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      (∑ i ∈ s, variance (X i) μ) / (((s.card : ℝ) * t) ^ 2) := h
    _ ≤ ((s.card : ℝ) * V) / (((s.card : ℝ) * t) ^ 2) := by
      apply div_le_div_of_nonneg_right
      · simpa only [← nsmul_eq_mul, ← Finset.sum_const] using
          (Finset.sum_le_sum fun i hi => hvariance i hi)
      · positivity
    _ = V / ((s.card : ℝ) * t ^ 2) := by
      have hcard : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hs)
      field_simp

/-- Upper-tail form used for a non-centered envelope average.

If independent variables have expectations at most `Kq`, variances at most
`K2²`, and `K2 ≤ Kq`, then their average exceeds `2 Kq` with probability at
most `δ` whenever `1 / δ ≤ |s|`.  The explicit constants expose the exact
Chebyshev step used by polynomial-envelope arguments.
@isnad1 id=le.10h8v.s8.23632135f4f1 from=translated src=- shape=7fae0aaa vocab=5b9f0de3
-/
theorem chebyshev_finset_average_gt_two_mul_le
    [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty)
    {K2 Kq δ : ℝ} (hK2 : 0 ≤ K2) (hKq : 0 < Kq)
    (hK2q : K2 ≤ Kq)
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hmean : ∀ i ∈ s, μ[X i] ≤ Kq)
    (hvariance : ∀ i ∈ s, variance (X i) μ ≤ K2 ^ 2)
    (hδ : 0 < δ) (hsize : 1 / δ ≤ (s.card : ℝ)) :
    μ.real {ω | 2 * Kq < (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤ δ := by
  let Xc : ι → Ω → ℝ := fun i ω => X i ω - μ[X i]
  let N : ℝ := s.card
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast s.card_pos.mpr hs
  have hcenter : ∀ i ∈ s, μ[Xc i] = 0 := by
    intro i hi
    dsimp only [Xc]
    rw [integral_sub ((hX i hi).integrable one_le_two) (integrable_const _),
      integral_const]
    simp
  have hXc : ∀ i ∈ s, MemLp (Xc i) 2 μ := by
    intro i hi
    exact (hX i hi).sub (memLp_const _)
  have hindepCenter : iIndepFun Xc μ := by
    have hcomp := h_indep.comp
      (fun i (x : ℝ) => x - μ[X i])
      (fun _i => measurable_id.sub measurable_const)
    simpa only [Xc, Function.comp_def] using hcomp
  have hvarCenter : ∀ i ∈ s, variance (Xc i) μ ≤ K2 ^ 2 := by
    intro i hi
    rw [show variance (Xc i) μ = variance (X i) μ by
      exact variance_sub_const (hX i hi).aestronglyMeasurable μ[X i]]
    exact hvariance i hi
  have htail := chebyshev_finset_average_abs_real_of_variance_le
    Xc hindepCenter s hs hXc hcenter hvarCenter hKq
  have hmeanAvg : (∑ i ∈ s, μ[X i]) / N ≤ Kq := by
    rw [div_le_iff₀ hN]
    calc
      (∑ i ∈ s, μ[X i]) ≤ ∑ _i ∈ s, Kq :=
        Finset.sum_le_sum fun i hi => hmean i hi
      _ = Kq * N := by
        simp [Finset.sum_const, nsmul_eq_mul, N, mul_comm]
  have hsubset :
      {ω | 2 * Kq < (∑ i ∈ s, X i ω) / (s.card : ℝ)} ⊆
      {ω | Kq ≤ |(∑ i ∈ s, Xc i ω) / (s.card : ℝ)|} := by
    intro ω hω
    change 2 * Kq < (∑ i ∈ s, X i ω) / (s.card : ℝ) at hω
    have hcenterAvg :
        (∑ i ∈ s, Xc i ω) / (s.card : ℝ) =
          (∑ i ∈ s, X i ω) / (s.card : ℝ) -
            (∑ i ∈ s, μ[X i]) / (s.card : ℝ) := by
      dsimp only [Xc]
      rw [Finset.sum_sub_distrib]
      ring
    have hdev : Kq <
        (∑ i ∈ s, Xc i ω) / (s.card : ℝ) := by
      rw [hcenterAvg]
      dsimp only [N] at hmeanAvg
      linarith
    exact hdev.le.trans (le_abs_self _)
  have hbad :
      μ.real {ω | 2 * Kq <
        (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
          K2 ^ 2 / ((s.card : ℝ) * Kq ^ 2) :=
    (measureReal_mono hsubset (by finiteness)).trans htail
  have hsq : K2 ^ 2 ≤ Kq ^ 2 :=
    (sq_le_sq₀ hK2 hKq.le).2 hK2q
  have hone_div : 1 / N ≤ δ := by
    rw [div_le_iff₀ hN]
    have hone : 1 ≤ δ * N := by
      have := (div_le_iff₀ hδ).1 hsize
      dsimp only [N]
      nlinarith
    linarith
  calc
    μ.real {ω | 2 * Kq <
        (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
        K2 ^ 2 / ((s.card : ℝ) * Kq ^ 2) := hbad
    _ ≤ Kq ^ 2 / (N * Kq ^ 2) := by
      dsimp only [N]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    _ = 1 / N := by field_simp [hKq.ne']
    _ ≤ δ := hone_div

end ProbabilityTheory

namespace RandomSetTheory

variable {Ω ι E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Polynomial directional tail for an empirical Minkowski average.  This
result uses only finite absolute moments; independence and centering are not
needed.  Consequently its scalar input is the deterministic convexity bound
on the moment of an average, rather than a Rosenthal/Fuk--Nagaev estimate.
@isnad1 id=le.7h10v.s8.e508a46d121e from=translated src=- shape=25a9cd0d vocab=94e79067
-/
theorem minkowskiAverage_support_markov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    (h_meas : ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_moment : ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L u i ω| ^ q) μ)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      (∑ i ∈ s, ProbabilityTheory.absoluteMoment
        (directionalSupportDeviation S L u i) q μ) /
          ((s.card : ℝ) * t ^ q) := by
  have htail := ProbabilityTheory.markov_finset_average_abs_real
    (directionalSupportDeviation S L u) s hs hq h_meas h_moment ht
  have hset :
      {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} =
      {ω | t ≤ |(∑ i ∈ s, directionalSupportDeviation S L u i ω) /
        (s.card : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L s hs hScompact hSne]
  rw [hset]
  exact htail

/-- Directional polynomial tail under explicit bounds on the individual
absolute moments.  The bounds `m i` may vary with the sample index but are
uniform in the selected direction.
@isnad1 id=le.8h11v.s8.d30b6b3c63f0 from=translated src=- shape=458c7f11 vocab=94e79067
-/
theorem minkowskiAverage_support_markov_of_moment_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (s : Finset ι) (hs : s.Nonempty) (m : ι → ℝ)
    {q : ℕ} (hq : 0 < q)
    (h_meas : ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_moment : ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L u i ω| ^ q) μ)
    (h_moment_le : ∀ i ∈ s, ProbabilityTheory.absoluteMoment
      (directionalSupportDeviation S L u i) q μ ≤ m i)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      (∑ i ∈ s, m i) / ((s.card : ℝ) * t ^ q) := by
  have h := minkowskiAverage_support_markov S L u s hs hq h_meas h_moment
    hScompact hSne ht
  refine h.trans ?_
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun i hi => h_moment_le i hi
  · positivity

/-- Common-moment directional specialization with the explicit polynomial
tail `M / t^q`.
@isnad1 id=le.8h11v.s8.30aa19247d6f from=translated src=- shape=8e461439 vocab=9560c4d1
-/
theorem minkowskiAverage_support_markov_of_common_moment_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    (h_meas : ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L u i) μ)
    (h_moment : ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L u i ω| ^ q) μ)
    {M : ℝ}
    (h_moment_le : ∀ i ∈ s, ProbabilityTheory.absoluteMoment
      (directionalSupportDeviation S L u i) q μ ≤ M)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤ M / t ^ q := by
  have h := minkowskiAverage_support_markov_of_moment_le
    S L u s hs (fun _ => M) hq h_meas h_moment h_moment_le
      hScompact hSne ht
  calc
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      (∑ _i ∈ s, M) / ((s.card : ℝ) * t ^ q) := h
    _ = M / t ^ q := by
      have hcard : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hs)
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Finite-net Hausdorff tail obtained from finite directional moments.

This is a union-bound theorem: the factor `N.card` is genuine, and no
independence across directions is assumed.  It should not be confused with
the sharper Fuk--Nagaev/chaining rate, which needs additional symmetrization
and empirical-process input.
@isnad1 id=le.16h14v.s9.8bfa42580eae from=translated src=- shape=894ada11 vocab=249db46a
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_of_moment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) (m : ι → ℝ)
    {q : ℕ} (hq : 0 < q)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 < t)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (h_meas : ∀ v ∈ N, ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L v i) μ)
    (h_moment : ∀ v ∈ N, ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L v i ω| ^ q) μ)
    (h_moment_le : ∀ v ∈ N, ∀ i ∈ s,
      ProbabilityTheory.absoluteMoment
        (directionalSupportDeviation S L v i) q μ ≤ m i) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * ((∑ i ∈ s, m i) / ((s.card : ℝ) * t ^ q)) := by
  obtain ⟨v₀, hv₀, _hv₀dist⟩ := hnet (0 : E) (by simp)
  have hm_nonneg : ∀ i ∈ s, 0 ≤ m i := by
    intro i hi
    exact (ProbabilityTheory.absoluteMoment_nonneg
      (directionalSupportDeviation S L v₀ i) q μ).trans
        (h_moment_le v₀ hv₀ i hi)
  have hrisk : 0 ≤ (∑ i ∈ s, m i) / ((s.card : ℝ) * t ^ q) :=
    div_nonneg (Finset.sum_nonneg hm_nonneg) (by positivity)
  apply measureReal_hausdorffDist_gt_le_finset_support
    (μ := μ) (fun ω => minkowskiAverage s (fun i => S i ω)) (fun _ => L)
    (fun ω => isCompact_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hScompact i ω))
    (fun _ => hLcompact)
    (fun ω => nonempty_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSne i ω))
    (fun _ => hLne)
    (fun ω => convex_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSconv i ω))
    (fun _ => hLconv)
    (fun ω x hx => norm_le_radius_of_mem_nonempty_minkowskiAverage s hs
      (fun i => S i ω) (fun i hi => hRS i ω) hx)
    (fun _ => hRL) heps ht.le hrisk N hnet
  intro v hv
  calc
    μ.real {ω | t < |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
        supportFunction L v|} ≤
        μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
          supportFunction L v|} := by
      apply measureReal_mono
      · intro ω hω
        change t < |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
          supportFunction L v| at hω
        change t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) v -
          supportFunction L v|
        exact hω.le
      · finiteness
    _ ≤ (∑ i ∈ s, m i) / ((s.card : ℝ) * t ^ q) :=
      minkowskiAverage_support_markov_of_moment_le S L v s hs m hq
        (h_meas v hv) (h_moment v hv) (h_moment_le v hv)
        (fun i _hi ω => hScompact i ω)
        (fun i _hi ω => hSne i ω) ht

/-- Common-moment finite-net bound with the transparent union-bound form
`N.card * (M / t^q)`.
@isnad1 id=le.16h14v.s9.0a291484ea44 from=translated src=- shape=966421da vocab=f77278a6
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_of_common_moment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    {RS RL eps t M : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 < t)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (h_meas : ∀ v ∈ N, ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L v i) μ)
    (h_moment : ∀ v ∈ N, ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L v i ω| ^ q) μ)
    (h_moment_le : ∀ v ∈ N, ∀ i ∈ s,
      ProbabilityTheory.absoluteMoment
        (directionalSupportDeviation S L v i) q μ ≤ M) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * (M / t ^ q) := by
  have h := hausdorffDist_minkowskiAverage_risk_bound_of_moment
    S L s hs (fun _ => M) hq hScompact hSne hSconv hLcompact hLne hLconv
      hRS hRL heps ht N hnet h_meas h_moment h_moment_le
  calc
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * ((∑ _i ∈ s, M) / ((s.card : ℝ) * t ^ q)) := h
    _ = N.card * (M / t ^ q) := by
      congr 1
      have hcard : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hs)
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Dimension-explicit version of the finite-moment Hausdorff bound.  A
volumetric net of the Euclidean unit ball contributes the entropy factor
`(1 + 2 / eps)^finrank`.  This is still a one-scale union bound, not a
chaining theorem.
@isnad1 id=le.15h13v.s9.e5676f529d47 from=translated src=- shape=6d32e75e vocab=5d89d908
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_dimensional_of_moment
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) (m : ι → ℝ)
    {q : ℕ} (hq : 0 < q)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (ht : 0 < t)
    (h_meas : ∀ v : E, ‖v‖ ≤ 1 → ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L v i) μ)
    (h_moment : ∀ v : E, ‖v‖ ≤ 1 → ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L v i ω| ^ q) μ)
    (h_moment_le : ∀ v : E, ‖v‖ ≤ 1 → ∀ i ∈ s,
      ProbabilityTheory.absoluteMoment
        (directionalSupportDeviation S L v i) q μ ≤ m i) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      (1 + 2 / eps) ^ Module.finrank ℝ E *
        ((∑ i ∈ s, m i) / ((s.card : ℝ) * t ^ q)) := by
  have hm_nonneg : ∀ i ∈ s, 0 ≤ m i := by
    intro i hi
    exact (ProbabilityTheory.absoluteMoment_nonneg
      (directionalSupportDeviation S L (0 : E) i) q μ).trans
        (h_moment_le (0 : E) (by simp) i hi)
  have hrisk : 0 ≤ (∑ i ∈ s, m i) / ((s.card : ℝ) * t ^ q) :=
    div_nonneg (Finset.sum_nonneg hm_nonneg) (by positivity)
  obtain ⟨N, hN, hnet, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  have hprob := hausdorffDist_minkowskiAverage_risk_bound_of_moment
    S L s hs m hq hScompact hSne hSconv hLcompact hLne hLconv
    hRS hRL heps.le ht N hnet
    (fun v hv => h_meas v (hN v hv))
    (fun v hv => h_moment v (hN v hv))
    (fun v hv => h_moment_le v (hN v hv))
  exact hprob.trans (mul_le_mul_of_nonneg_right hcard hrisk)

/-- Dimension-explicit common-moment bound.  This is the precise
`(1 + 2 / eps)^dim * M / t^q` one-net Markov estimate.
@isnad1 id=le.15h13v.s9.51f7b9731778 from=translated src=- shape=9f95d172 vocab=f0abc3dd
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_dimensional_of_common_moment
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    {q : ℕ} (hq : 0 < q)
    {RS RL eps t M : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (ht : 0 < t)
    (h_meas : ∀ v : E, ‖v‖ ≤ 1 → ∀ i ∈ s,
      AEMeasurable (directionalSupportDeviation S L v i) μ)
    (h_moment : ∀ v : E, ‖v‖ ≤ 1 → ∀ i ∈ s, Integrable
      (fun ω => |directionalSupportDeviation S L v i ω| ^ q) μ)
    (h_moment_le : ∀ v : E, ‖v‖ ≤ 1 → ∀ i ∈ s,
      ProbabilityTheory.absoluteMoment
        (directionalSupportDeviation S L v i) q μ ≤ M) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      (1 + 2 / eps) ^ Module.finrank ℝ E * (M / t ^ q) := by
  have h := hausdorffDist_minkowskiAverage_risk_bound_dimensional_of_moment
    S L s hs (fun _ => M) hq hScompact hSne hSconv hLcompact hLne hLconv
      hRS hRL heps ht h_meas h_moment h_moment_le
  calc
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      (1 + 2 / eps) ^ Module.finrank ℝ E *
        ((∑ _i ∈ s, M) / ((s.card : ℝ) * t ^ q)) := h
    _ = (1 + 2 / eps) ^ Module.finrank ℝ E * (M / t ^ q) := by
      congr 1
      have hcard : (s.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr hs)
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-! ## Variance-additive specialization -/

/-- Directional Chebyshev inequality for independent centered support
deviations.  Variance additivity improves the denominator from the crude
moment/triangle bound to `((card s) * t)^2`.
@isnad1 id=le.7h9v.s8.a370c0049db8 from=translated src=- shape=ff7ea26c vocab=09744474
-/
theorem minkowskiAverage_support_chebyshev
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (s : Finset ι) (hs : s.Nonempty)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (hL2 : ∀ i ∈ s, MemLp (directionalSupportDeviation S L u i) 2 μ)
    (h_centered : ∀ i ∈ s,
      μ[directionalSupportDeviation S L u i] = 0)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      (∑ i ∈ s, ProbabilityTheory.variance
        (directionalSupportDeviation S L u i) μ) /
          (((s.card : ℝ) * t) ^ 2) := by
  have htail := ProbabilityTheory.chebyshev_finset_average_abs_real
    (directionalSupportDeviation S L u) h_indep s hs hL2 h_centered ht
  have hset :
      {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} =
      {ω | t ≤ |(∑ i ∈ s, directionalSupportDeviation S L u i ω) /
        (s.card : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L s hs hScompact hSne]
  rw [hset]
  exact htail

/-- Directional Chebyshev inequality with explicit upper bounds `v i` on
the directional variances.
@isnad1 id=le.8h10v.s8.0ce1b3df9ead from=translated src=- shape=55414783 vocab=09744474
-/
theorem minkowskiAverage_support_chebyshev_of_variance_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (s : Finset ι) (hs : s.Nonempty) (v : ι → ℝ)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (hL2 : ∀ i ∈ s, MemLp (directionalSupportDeviation S L u i) 2 μ)
    (h_centered : ∀ i ∈ s,
      μ[directionalSupportDeviation S L u i] = 0)
    (h_variance_le : ∀ i ∈ s, ProbabilityTheory.variance
      (directionalSupportDeviation S L u i) μ ≤ v i)
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      (∑ i ∈ s, v i) / (((s.card : ℝ) * t) ^ 2) := by
  have h := minkowskiAverage_support_chebyshev S L u s hs h_indep hL2
    h_centered hScompact hSne ht
  refine h.trans ?_
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun i hi => h_variance_le i hi
  · positivity

/-- Finite-net Hausdorff Chebyshev bound.  For a common variance bound
`v i = σ²`, the directional factor simplifies to `σ² / (card s * t²)`.
@isnad1 id=le.16h13v.s9.d44cdae73084 from=translated src=- shape=c5360d3a vocab=53b4eae6
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_of_variance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) (v : ι → ℝ)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 < t)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ w ∈ N, dist u w ≤ eps)
    (h_indep : ∀ w ∈ N, ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hL2 : ∀ w ∈ N, ∀ i ∈ s,
      MemLp (directionalSupportDeviation S L w i) 2 μ)
    (h_centered : ∀ w ∈ N, ∀ i ∈ s,
      μ[directionalSupportDeviation S L w i] = 0)
    (h_variance_le : ∀ w ∈ N, ∀ i ∈ s,
      ProbabilityTheory.variance
        (directionalSupportDeviation S L w i) μ ≤ v i) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * ((∑ i ∈ s, v i) / (((s.card : ℝ) * t) ^ 2)) := by
  obtain ⟨w₀, hw₀, _hw₀dist⟩ := hnet (0 : E) (by simp)
  have hv_nonneg : ∀ i ∈ s, 0 ≤ v i := by
    intro i hi
    exact (ProbabilityTheory.variance_nonneg
      (directionalSupportDeviation S L w₀ i) μ).trans
        (h_variance_le w₀ hw₀ i hi)
  have hrisk : 0 ≤ (∑ i ∈ s, v i) / (((s.card : ℝ) * t) ^ 2) :=
    div_nonneg (Finset.sum_nonneg hv_nonneg) (sq_nonneg _)
  apply measureReal_hausdorffDist_gt_le_finset_support
    (μ := μ) (fun ω => minkowskiAverage s (fun i => S i ω)) (fun _ => L)
    (fun ω => isCompact_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hScompact i ω))
    (fun _ => hLcompact)
    (fun ω => nonempty_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSne i ω))
    (fun _ => hLne)
    (fun ω => convex_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSconv i ω))
    (fun _ => hLconv)
    (fun ω x hx => norm_le_radius_of_mem_nonempty_minkowskiAverage s hs
      (fun i => S i ω) (fun i hi => hRS i ω) hx)
    (fun _ => hRL) heps ht.le hrisk N hnet
  intro w hw
  calc
    μ.real {ω | t < |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
        supportFunction L w|} ≤
        μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w|} := by
      apply measureReal_mono
      · intro ω hω
        change t < |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w| at hω
        change t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w|
        exact hω.le
      · finiteness
    _ ≤ (∑ i ∈ s, v i) / (((s.card : ℝ) * t) ^ 2) :=
      minkowskiAverage_support_chebyshev_of_variance_le S L w s hs v
        (h_indep w hw) (hL2 w hw) (h_centered w hw) (h_variance_le w hw)
        (fun i _hi ω => hScompact i ω)
        (fun i _hi ω => hSne i ω) ht

/-- Dimension-explicit Hausdorff Chebyshev bound obtained from the
volumetric unit-ball net.
@isnad1 id=le.15h12v.s9.80a2185db4c0 from=translated src=- shape=f80cac1d vocab=4627515f
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_dimensional_of_variance
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty) (v : ι → ℝ)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (ht : 0 < t)
    (h_indep : ∀ w : E, ‖w‖ ≤ 1 → ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hL2 : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ s,
      MemLp (directionalSupportDeviation S L w i) 2 μ)
    (h_centered : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ s,
      μ[directionalSupportDeviation S L w i] = 0)
    (h_variance_le : ∀ w : E, ‖w‖ ≤ 1 → ∀ i ∈ s,
      ProbabilityTheory.variance
        (directionalSupportDeviation S L w i) μ ≤ v i) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      (1 + 2 / eps) ^ Module.finrank ℝ E *
        ((∑ i ∈ s, v i) / (((s.card : ℝ) * t) ^ 2)) := by
  have hv_nonneg : ∀ i ∈ s, 0 ≤ v i := by
    intro i hi
    exact (ProbabilityTheory.variance_nonneg
      (directionalSupportDeviation S L (0 : E) i) μ).trans
        (h_variance_le (0 : E) (by simp) i hi)
  have hrisk : 0 ≤ (∑ i ∈ s, v i) / (((s.card : ℝ) * t) ^ 2) :=
    div_nonneg (Finset.sum_nonneg hv_nonneg) (sq_nonneg _)
  obtain ⟨N, hN, hnet, hcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  have hprob := hausdorffDist_minkowskiAverage_risk_bound_of_variance
    S L s hs v hScompact hSne hSconv hLcompact hLne hLconv
    hRS hRL heps.le ht N hnet
    (fun w hw => h_indep w (hN w hw))
    (fun w hw => hL2 w (hN w hw))
    (fun w hw => h_centered w (hN w hw))
    (fun w hw => h_variance_le w (hN w hw))
  exact hprob.trans (mul_le_mul_of_nonneg_right hcard hrisk)

end RandomSetTheory
