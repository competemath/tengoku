/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.MomentConcentration
import Tengoku.Seed.Probability.StrongLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Truncation reduction for heavy-tailed sums

The first deterministic step of every Fuk--Nagaev argument separates a
large deviation of an unbounded sum into two alternatives:

* at least one summand exceeds the truncation level;
* the sum of the centred truncated variables is large.

This file proves the exact algebraic identity, the corresponding event
inclusion, its finite-union probability bound, and the polynomial estimate
of the exceptional-observation term from arbitrary absolute moments.  A
Bernstein or Hoeffding estimate for the remaining bounded sum can be inserted
afterwards.  No claim of the final optimal Fuk--Nagaev inequality is made.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {Omega I : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A scalar random variable truncated at level `y` and centred by its own
expectation.-/
def centeredTruncation (X : Omega → ℝ) (y : ℝ)
    (mu : Measure Omega) (omega : Omega) : ℝ :=
  truncation X y omega - ∫ z, truncation X y z ∂mu

/-- The deterministic bias introduced when every summand is truncated.-/
def totalTruncationBias (s : Finset I) (X : I → Omega → ℝ)
    (y : ℝ) (mu : Measure Omega) : ℝ :=
  ∑ i ∈ s, ((∫ z, truncation (X i) y z ∂mu) - ∫ z, X i z ∂mu)

/-- Truncation and deterministic recentering preserve almost-everywhere
measurability.
@isnad1 id=aemeasur.1h4v.s5.4c2985e28fff from=translated src=- shape=f41c30ff vocab=e88d8854
-/
theorem aemeasurable_centeredTruncation [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : AEMeasurable X mu) (y : ℝ) :
    AEMeasurable (centeredTruncation X y mu) mu := by
  unfold centeredTruncation
  exact hX.aestronglyMeasurable.truncation.aemeasurable.sub aemeasurable_const

/-- A centred truncation is integrable on every finite measure space.
@isnad1 id=integrab.1h4v.s5.852771545d0c from=translated src=- shape=6042859a vocab=f959e047
-/
theorem integrable_centeredTruncation [IsFiniteMeasure mu]
    {X : Omega → ℝ} (hX : AEMeasurable X mu) (y : ℝ) :
    Integrable (centeredTruncation X y mu) mu := by
  unfold centeredTruncation
  exact hX.aestronglyMeasurable.integrable_truncation.sub (integrable_const _)

/-- On a probability space, centring a truncation gives integral zero.
@isnad1 id=eq.1h4v.s5.5fdf158cbde3 from=translated src=- shape=62bc5b50 vocab=6c14d832
-/
theorem integral_centeredTruncation [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : AEMeasurable X mu) (y : ℝ) :
    ∫ omega, centeredTruncation X y mu omega ∂mu = 0 := by
  have htrunc : Integrable (truncation X y) mu :=
    hX.aestronglyMeasurable.integrable_truncation
  change ∫ omega, (truncation X y omega - ∫ z, truncation X y z ∂mu) ∂mu = 0
  rw [integral_sub htrunc (integrable_const _)]
  simp

/-- The mean of a truncation is bounded by the truncation level.
@isnad1 id=le.0h4v.s5.02daa4484e31 from=translated src=- shape=f31b976b vocab=c245bafb
-/
theorem abs_integral_truncation_le [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (y : ℝ) :
    |∫ omega, truncation X y omega ∂mu| ≤ |y| := by
  have h := norm_integral_le_of_norm_le_const (μ := mu)
    (f := truncation X y) (C := |y|)
    (ae_of_all mu fun omega => by
      simpa only [Real.norm_eq_abs] using abs_truncation_le_bound X y omega)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- A centred truncation at `y` takes values in the deterministic interval
`[-2|y|, 2|y|]`.
@isnad1 id=mem.0h5v.s6.2481f3c4aa75 from=translated src=- shape=ca54bfcf vocab=a6371d30
-/
theorem centeredTruncation_mem_Icc [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (y : ℝ) (omega : Omega) :
    centeredTruncation X y mu omega ∈ Icc (-2 * |y|) (2 * |y|) := by
  have hpoint : |truncation X y omega| ≤ |y| :=
    abs_truncation_le_bound X y omega
  have hmean : |∫ z, truncation X y z ∂mu| ≤ |y| :=
    abs_integral_truncation_le X y
  have habs : |centeredTruncation X y mu omega| ≤ 2 * |y| := by
    calc
      |centeredTruncation X y mu omega| ≤
          |truncation X y omega| + |∫ z, truncation X y z ∂mu| := by
        simpa only [centeredTruncation] using
          abs_sub (truncation X y omega) (∫ z, truncation X y z ∂mu)
      _ ≤ |y| + |y| := add_le_add hpoint hmean
      _ = 2 * |y| := by ring
  rw [Set.mem_Icc]
  constructor <;> linarith [abs_le.mp habs]

/-- Coordinatewise measurable transformations preserve independence; in
particular an independent family stays independent after truncation and
recentering.
@isnad1 id=iindepfu.1h5v.s5.64962e4a81fb from=translated src=- shape=ac96f439 vocab=ce12fa82
-/
theorem iIndepFun_centeredTruncation
    (X : I → Omega → ℝ) (y : ℝ)
    (h_indep : iIndepFun X mu) :
    iIndepFun (fun i => centeredTruncation (X i) y mu) mu := by
  let g : I → ℝ → ℝ := fun i x =>
    truncation id y x - ∫ z, truncation (X i) y z ∂mu
  have htrunc : Measurable (truncation id y) := by
    simpa only [truncation, Function.comp_id] using
      (measurable_id.indicator measurableSet_Ioc)
  have hg : ∀ i, Measurable (g i) := fun i => htrunc.sub measurable_const
  exact (h_indep.comp g hg).congr (fun i => ae_of_all mu fun omega => by
    simp only [g, centeredTruncation, Function.comp_apply, truncation,
      id_eq])

/-- Hoeffding's inequality for a sum of centred truncations.  The interval
width is `4|y|`, hence the explicit variance proxy `4 * card(s) * y²` and
the denominator `8 * card(s) * y²`.
@isnad1 id=le.3h7v.s7.8ab3ee8af505 from=translated src=- shape=d4aff55c vocab=4d44944d
-/
theorem measureReal_sum_centeredTruncation_abs_ge_le
    [IsProbabilityMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ)
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, AEMeasurable (X i) mu)
    {y t : ℝ} (ht : 0 ≤ t) :
    mu.real {omega | t ≤
        |∑ i ∈ s, centeredTruncation (X i) y mu omega|} ≤
      2 * exp (-t ^ 2 / (8 * (s.card : ℝ) * y ^ 2)) := by
  have hhoeff := hoeffding_finset_sum_abs_real
    (μ := mu)
    (X := fun i => centeredTruncation (X i) y mu)
    (a := fun _ => -2 * |y|) (b := fun _ => 2 * |y|)
    (iIndepFun_centeredTruncation X y h_indep)
    (fun i => aemeasurable_centeredTruncation (h_meas i) y)
    (fun i => ae_of_all mu fun omega => centeredTruncation_mem_Icc (X i) y omega)
    (fun i => integral_centeredTruncation (h_meas i) y)
    s ht
  have hproxy :
      (↑(∑ i ∈ s,
        (((‖(2 * |y|) - (-2 * |y|)‖₊ / (2 : NNReal)) ^ (2 : ℕ)) :
          NNReal) : NNReal) : ℝ) = 4 * (s.card : ℝ) * y ^ 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hnorm : ‖2 * |y| - -2 * |y|‖₊ = 4 * ‖y‖₊ := by
      ext
      simp [Real.norm_eq_abs, abs_of_nonneg]
      ring_nf
    rw [hnorm]
    push_cast
    rw [Real.norm_eq_abs]
    ring_nf
    rw [sq_abs]
  rw [hproxy] at hhoeff
  convert hhoeff using 1
  all_goals ring_nf

omit [MeasurableSpace Omega] in
/-- The pointwise truncation error is controlled by the `q`-th power tail.
@isnad1 id=le.2h5v.s6.250c7d11dbb1 from=translated src=- shape=6e635d77 vocab=99ecd930
-/
theorem abs_truncation_sub_le_abs_pow_div
    (X : Omega → ℝ) {q : ℕ} (hq : 1 ≤ q) {y : ℝ} (hy : 0 < y)
    (omega : Omega) :
    |truncation X y omega - X omega| ≤ |X omega| ^ q / y ^ (q - 1) := by
  by_cases hsmall : |X omega| < y
  · rw [truncation_eq_self hsmall]
    simp only [sub_self, abs_zero]
    exact div_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg hy.le _)
  · have herror : |truncation X y omega - X omega| ≤ |X omega| := by
      simp only [truncation, Set.indicator, id, Function.comp_apply]
      split_ifs <;> simp
    have hlarge : y ≤ |X omega| := le_of_not_gt hsmall
    have hden : 0 < y ^ (q - 1) := pow_pos hy _
    refine herror.trans ((le_div_iff₀ hden).2 ?_)
    calc
      |X omega| * y ^ (q - 1) ≤ |X omega| * |X omega| ^ (q - 1) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hy.le hlarge (q - 1)) (abs_nonneg _)
      _ = |X omega| ^ q := by
        rw [← pow_succ']
        congr 1
        omega

/-- The mean removed by truncation has the classical `q`-moment bound.
@isnad1 id=le.4h5v.s7.d5cf217a0abc from=translated src=- shape=d4ddc471 vocab=7b437d66
-/
theorem abs_integral_truncation_sub_integral_le_absoluteMoment_div
    [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : AEMeasurable X mu) {q : ℕ} (hq : 1 ≤ q)
    (hXq : Integrable (fun omega ↦ |X omega| ^ q) mu)
    {y : ℝ} (hy : 0 < y) :
    |(∫ omega, truncation X y omega ∂mu) - ∫ omega, X omega ∂mu| ≤
      absoluteMoment X q mu / y ^ (q - 1) := by
  have htrunc : Integrable (truncation X y) mu :=
    hX.aestronglyMeasurable.integrable_truncation
  have hXint : Integrable X mu := by
    apply (integrable_norm_iff hX.aestronglyMeasurable).1
    have hpow : Integrable (fun omega ↦ ‖X omega‖ ^ q) mu := by
      simpa only [Real.norm_eq_abs] using hXq
    simpa only [pow_one] using
      (integrable_norm_pow_of_le hX.aestronglyMeasurable hq hpow :
        Integrable (fun omega ↦ ‖X omega‖ ^ 1) mu)
  rw [← integral_sub htrunc hXint]
  simpa only [Real.norm_eq_abs, integral_div, absoluteMoment] using
    (norm_integral_le_of_norm_le
      (f := fun omega ↦ truncation X y omega - X omega)
      (hXq.div_const (y ^ (q - 1)))
      (ae_of_all mu fun omega ↦ by
        simpa only [Real.norm_eq_abs] using
          abs_truncation_sub_le_abs_pow_div X hq hy omega))

/-- The total deterministic truncation bias is bounded by the sum of
`q`-th absolute moments divided by `y^(q-1)`.
@isnad1 id=le.4h7v.s7.a24e07741d45 from=translated src=- shape=1f267a9a vocab=6efbf94f
-/
theorem abs_totalTruncationBias_le_sum_absoluteMoment_div
    [IsProbabilityMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) mu)
    {q : ℕ} (hq : 1 ≤ q)
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {y : ℝ} (hy : 0 < y) :
    |totalTruncationBias s X y mu| ≤
      (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1) := by
  unfold totalTruncationBias
  calc
    |∑ i ∈ s,
        ((∫ z, truncation (X i) y z ∂mu) - ∫ z, X i z ∂mu)| ≤
        ∑ i ∈ s,
          |(∫ z, truncation (X i) y z ∂mu) - ∫ z, X i z ∂mu| :=
      Finset.abs_sum_le_sum_abs _ s
    _ ≤ ∑ i ∈ s, absoluteMoment (X i) q mu / y ^ (q - 1) := by
      gcongr with i hi
      exact abs_integral_truncation_sub_integral_le_absoluteMoment_div
        (h_meas i hi) hq (hXq i hi) hy
    _ = (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1) := by
      rw [Finset.sum_div]

/-- On a realization where no summand reaches the truncation level, the
original centred sum is the centred truncated sum plus the deterministic
truncation bias.
@isnad1 id=eq.1h7v.s6.00acb3858556 from=translated src=- shape=14356cdb vocab=bf00adea
-/
theorem sum_sub_integral_eq_sum_centeredTruncation_add_bias
    (s : Finset I) (X : I → Omega → ℝ) (y : ℝ) (omega : Omega)
    (hsmall : ∀ i ∈ s, |X i omega| < y) :
    (∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)) =
      (∑ i ∈ s, centeredTruncation (X i) y mu omega) +
        totalTruncationBias s X y mu := by
  unfold totalTruncationBias
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [centeredTruncation, truncation_eq_self (hsmall i hi)]
  ring

/-- **Fuk--Nagaev event decomposition.** A centred sum above the threshold
`t + |bias|` forces either one raw observation above `y`, or the centred
truncated sum above `t`.
@isnad1 id=le.0h7v.s7.743bdc94d2ad from=translated src=- shape=82a223b0 vocab=eeba3faf
-/
theorem centered_sum_large_subset_iUnion_large_or_truncation
    (s : Finset I) (X : I → Omega → ℝ) (y t : ℝ) :
    {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ⊆
      (⋃ i ∈ s, {omega | y ≤ |X i omega|}) ∪
        {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := by
  intro omega homega
  by_cases hlarge : ∃ i ∈ s, y ≤ |X i omega|
  · left
    obtain ⟨i, hi, hiy⟩ := hlarge
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hiy⟩⟩
  · right
    have hsmall : ∀ i ∈ s, |X i omega| < y := by
      intro i hi
      exact lt_of_not_ge fun hiy ↦ hlarge ⟨i, hi, hiy⟩
    change t ≤ |∑ i ∈ s, centeredTruncation (X i) y mu omega|
    change t + |totalTruncationBias s X y mu| ≤
      |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)| at homega
    rw [sum_sub_integral_eq_sum_centeredTruncation_add_bias
      s X y omega hsmall] at homega
    by_contra hnot
    have htrunc :
        |∑ i ∈ s, centeredTruncation (X i) y mu omega| < t :=
      lt_of_not_ge hnot
    have hstrict :
        |(∑ i ∈ s, centeredTruncation (X i) y mu omega) +
            totalTruncationBias s X y mu| <
          t + |totalTruncationBias s X y mu| :=
      (abs_add_le _ _).trans_lt (add_lt_add_left htrunc _)
    exact (not_lt_of_ge homega) hstrict

/-- Probability form of the truncation decomposition.  It is purely a union
bound and does not require measurability hypotheses beyond those implicit in
`measureReal`.
@isnad1 id=le.0h7v.s7.54ad054c9413 from=translated src=- shape=ed049257 vocab=964077d0
-/
theorem measureReal_centered_sum_large_le_sum_large_add_truncation
    [IsFiniteMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) (y t : ℝ) :
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (∑ i ∈ s, mu.real {omega | y ≤ |X i omega|}) +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := by
  let U : Set Omega := ⋃ i ∈ s, {omega | y ≤ |X i omega|}
  let T : Set Omega := {omega | t ≤
    |∑ i ∈ s, centeredTruncation (X i) y mu omega|}
  calc
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
        mu.real (U ∪ T) :=
      measureReal_mono
        (centered_sum_large_subset_iUnion_large_or_truncation s X y t)
    _ ≤ mu.real U + mu.real T := measureReal_union_le _ _
    _ ≤ (∑ i ∈ s, mu.real {omega | y ≤ |X i omega|}) +
        mu.real T := by
      apply add_le_add
      · simpa only [U] using (measureReal_biUnion_finset_le s
          fun i ↦ {omega | y ≤ |X i omega|})
      · exact le_rfl
    _ = (∑ i ∈ s, mu.real {omega | y ≤ |X i omega|}) +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := rfl

/-- Moment form of the Fuk--Nagaev reduction.  The heavy-tail contribution
is the transparent polynomial term `sum moments / y^q`; only the centred
truncated probability remains to be estimated.
@isnad1 id=le.2h8v.s8.907a489d6c24 from=translated src=- shape=eab1765a vocab=5cfe5f8c
-/
theorem measureReal_centered_sum_large_le_moment_div_add_truncation
    [IsFiniteMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) {q : ℕ}
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {y t : ℝ} (hy : 0 < y) :
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ q +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := by
  have hdecomp :=
    measureReal_centered_sum_large_le_sum_large_add_truncation
      (mu := mu) s X y t
  calc
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (∑ i ∈ s, mu.real {omega | y ≤ |X i omega|}) +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := hdecomp
    _ ≤ (∑ i ∈ s, absoluteMoment (X i) q mu / y ^ q) +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := by
      gcongr with i hi
      exact measureReal_abs_ge_le_absoluteMoment_div (X i) q (hXq i hi) hy
    _ = (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ q +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := by
      rw [Finset.sum_div]

/-- A scalar Fuk--Nagaev inequality with the deterministic truncation bias
kept explicit.  It combines the polynomial cost of exceptional observations
with Hoeffding's exponential bound for the bounded centred remainder.
@isnad1 id=le.5h8v.s8.663787d25ab3 from=translated src=- shape=f4a7dbd2 vocab=684d19e5
-/
theorem measureReal_centered_sum_large_le_moment_div_add_exp
    [IsProbabilityMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) {q : ℕ}
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, AEMeasurable (X i) mu)
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ q +
        2 * exp (-t ^ 2 / (8 * (s.card : ℝ) * y ^ 2)) := by
  have hreduction :=
    measureReal_centered_sum_large_le_moment_div_add_truncation
      (mu := mu) s X hXq (t := t) hy
  have hbounded := measureReal_sum_centeredTruncation_abs_ge_le
    (mu := mu) s X h_indep h_meas (y := y) ht
  exact hreduction.trans (add_le_add_right hbounded _)

/-- **Fuk--Nagaev bound with a completely explicit truncation bias.**
The threshold is shifted by the moment bound `sum E|X_i|^q / y^(q-1)`,
so the deterministic bias no longer appears in the statement.
@isnad1 id=le.6h8v.s8.be148d84f471 from=translated src=- shape=e5eedef7 vocab=6791dfd6
-/
theorem measureReal_centered_sum_large_le_moment_bias_add_exp
    [IsProbabilityMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) {q : ℕ}
    (hq : 1 ≤ q)
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, AEMeasurable (X i) mu)
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {y t : ℝ} (hy : 0 < y) (ht : 0 ≤ t) :
    mu.real {omega |
        t + (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1) ≤
          |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ q +
        2 * exp (-t ^ 2 / (8 * (s.card : ℝ) * y ^ 2)) := by
  have hbias := abs_totalTruncationBias_le_sum_absoluteMoment_div
    (mu := mu) s X (fun i hi ↦ h_meas i) hq hXq hy
  have hbase := measureReal_centered_sum_large_le_moment_div_add_exp
    (mu := mu) s X h_indep h_meas hXq hy ht
  exact (measureReal_mono (by
    intro omega homega
    change t + |totalTruncationBias s X y mu| ≤
      |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|
    change t + (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1) ≤
      |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)| at homega
    linarith)).trans hbase

/-- Unshifted-threshold form of the explicit Fuk--Nagaev bound.  The only
additional assumption says that the requested deviation `u` dominates the
moment-controlled truncation bias.
@isnad1 id=le.6h8v.s8.792034c3d1b3 from=translated src=- shape=62f8d40c vocab=6791dfd6
-/
theorem measureReal_centered_sum_ge_le_moment_div_add_exp
    [IsProbabilityMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) {q : ℕ}
    (hq : 1 ≤ q)
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, AEMeasurable (X i) mu)
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {y u : ℝ} (hy : 0 < y)
    (hu : (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1) ≤ u) :
    mu.real {omega | u ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ q +
        2 * exp (-(u -
          (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1)) ^ 2 /
            (8 * (s.card : ℝ) * y ^ 2)) := by
  let B : ℝ := (∑ i ∈ s, absoluteMoment (X i) q mu) / y ^ (q - 1)
  have hbias : |totalTruncationBias s X y mu| ≤ B := by
    simpa only [B] using abs_totalTruncationBias_le_sum_absoluteMoment_div
      (mu := mu) s X (fun i hi ↦ h_meas i) hq hXq hy
  have ht : 0 ≤ u - B := sub_nonneg.mpr (by simpa only [B] using hu)
  have hbase := measureReal_centered_sum_large_le_moment_div_add_exp
    (mu := mu) s X h_indep h_meas hXq hy ht
  have hmono :
      mu.real {omega | u ≤
          |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
        mu.real {omega | (u - B) + |totalTruncationBias s X y mu| ≤
          |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} :=
    measureReal_mono (by
      intro omega homega
      have hthreshold : (u - B) + |totalTruncationBias s X y mu| ≤ u := by
        linarith
      exact hthreshold.trans homega)
  simpa only [B] using hmono.trans hbase

/-- Common-moment simplification of the polynomial truncation term.
@isnad1 id=le.3h9v.s8.dd75bc78a93a from=translated src=- shape=2ea2d47b vocab=012b1613
-/
theorem measureReal_centered_sum_large_le_common_moment_add_truncation
    [IsFiniteMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) {q : ℕ}
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {M y t : ℝ} (hM : ∀ i ∈ s, absoluteMoment (X i) q mu ≤ M)
    (hy : 0 < y) :
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (s.card : ℝ) * M / y ^ q +
        mu.real {omega | t ≤
          |∑ i ∈ s, centeredTruncation (X i) y mu omega|} := by
  have h := measureReal_centered_sum_large_le_moment_div_add_truncation
    (mu := mu) s X hXq (t := t) hy
  refine h.trans ?_
  gcongr
  simpa [nsmul_eq_mul] using
    (Finset.sum_le_card_nsmul s
      (fun i ↦ absoluteMoment (X i) q mu) M hM)

/-- Common-moment version of the scalar Fuk--Nagaev bound.
@isnad1 id=le.6h9v.s8.82b12505b8dd from=translated src=- shape=1749b19b vocab=684d19e5
-/
theorem measureReal_centered_sum_large_le_common_moment_add_exp
    [IsProbabilityMeasure mu]
    (s : Finset I) (X : I → Omega → ℝ) {q : ℕ}
    (h_indep : iIndepFun X mu)
    (h_meas : ∀ i, AEMeasurable (X i) mu)
    (hXq : ∀ i ∈ s, Integrable (fun omega ↦ |X i omega| ^ q) mu)
    {M y t : ℝ} (hM : ∀ i ∈ s, absoluteMoment (X i) q mu ≤ M)
    (hy : 0 < y) (ht : 0 ≤ t) :
    mu.real {omega | t + |totalTruncationBias s X y mu| ≤
        |∑ i ∈ s, (X i omega - ∫ z, X i z ∂mu)|} ≤
      (s.card : ℝ) * M / y ^ q +
        2 * exp (-t ^ 2 / (8 * (s.card : ℝ) * y ^ 2)) := by
  have h := measureReal_centered_sum_large_le_moment_div_add_exp
    (mu := mu) s X h_indep h_meas hXq hy ht
  refine h.trans ?_
  gcongr
  simpa [nsmul_eq_mul] using
    (Finset.sum_le_card_nsmul s
      (fun i ↦ absoluteMoment (X i) q mu) M hM)

end ProbabilityTheory
