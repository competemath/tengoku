import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletTail
import Tengoku.Seed.NumberTheory.LSeries.RiemannZeta

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Pole-corrected ordered zeta truncations

Finite Euler summation is obtained by integrating complex-power variation on
each unit interval.  The estimates keep the pole correction explicit.
-/

noncomputable section

open Finset MeasureTheory Filter
open scoped Interval Topology

namespace TwinPrime.Analytic

private theorem intervalIntegrable_cpow_neg_positive (s : ℂ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a b := by
  apply intervalIntegral.intervalIntegrable_cpow (Or.inr ?_)
  rw [Set.uIcc_of_le hab]
  intro h
  exact ha.not_ge h.1

/-- Euler's error on a unit interval is bounded by the decrease of the
real power majorant across that interval.-/
theorem norm_cpow_neg_sub_integral_unit_le (s : ℂ) (hs : 0 < s.re)
    (a : ℝ) (ha : 0 < a) :
    ‖((a + 1 : ℝ) : ℂ) ^ (-s) -
        ∫ x : ℝ in a..a + 1, (x : ℂ) ^ (-s)‖ ≤
      (‖s‖ / s.re) * (a ^ (-s.re) - (a + 1) ^ (-s.re)) := by
  have hab : a ≤ a + 1 := by linarith
  have hi := intervalIntegrable_cpow_neg_positive s ha hab
  have heq : ((a + 1 : ℝ) : ℂ) ^ (-s) -
      (∫ x : ℝ in a..a + 1, (x : ℂ) ^ (-s)) =
      ∫ x : ℝ in a..a + 1, ((a + 1 : ℝ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const]
    simp
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := a + 1)
    (C := (‖s‖ / s.re) * (a ^ (-s.re) - (a + 1) ^ (-s.re)))
    (f := fun x : ℝ => ((a + 1 : ℝ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) ?_
  · simpa using h
  intro x hx
  rw [Set.uIoc_of_le hab] at hx
  apply (norm_cpow_neg_sub_le s hs (ha.trans hx.1) hx.2).trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (norm_nonneg _) hs.le)
  exact sub_le_sub_right
    (Real.rpow_le_rpow_of_nonpos ha hx.1.le (neg_nonpos.mpr hs.le)) _

/-- Finite Euler summation with a quantitative complex-power error.
The two endpoints may coincide.-/
theorem norm_sum_cpow_neg_sub_integral_Ioc_le (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs : 0 < s.re) :
    ‖(∑ n ∈ Ioc M N, (n : ℂ) ^ (-s)) -
        ∫ x : ℝ in (M : ℝ)..N, (x : ℂ) ^ (-s)‖ ≤
      (‖s‖ / s.re) * ((M : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    have hN0 : (0 : ℝ) < N := hM0.trans_le (by exact_mod_cast hMN)
    have hi := intervalIntegrable_cpow_neg_positive s hM0
      (show (M : ℝ) ≤ N by exact_mod_cast hMN)
    have hj := intervalIntegrable_cpow_neg_positive s hN0
      (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
    rw [sum_Ioc_succ_top hMN]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [← intervalIntegral.integral_add_adjacent_intervals hi hj]
    have hunit := norm_cpow_neg_sub_integral_unit_le s hs N hN0
    simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] at hunit
    have heq (a b c d : ℂ) : a + b - (c + d) = (a - c) + (b - d) := by ring
    rw [heq]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ (‖s‖ / s.re) * ((M : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re)) +
          (‖s‖ / s.re) * ((N : ℝ) ^ (-s.re) - ((N : ℝ) + 1) ^ (-s.re)) :=
        add_le_add ih hunit
      _ = _ := by ring

/-- A positive-length complex-power integral with the pole denominator exposed.-/
theorem integral_cpow_neg_eq_pole_difference (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs1 : s ≠ 1) :
    (∫ x : ℝ in (M : ℝ)..N, (x : ℂ) ^ (-s)) =
      (M : ℂ) ^ (1 - s) / (s - 1) - (N : ℂ) ^ (1 - s) / (s - 1) := by
  have hz : (0 : ℝ) ∉ Set.uIcc (M : ℝ) N := by
    rw [Set.uIcc_of_le (show (M : ℝ) ≤ N by exact_mod_cast hMN)]
    intro h
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    exact hM0.not_ge h.1
  rw [integral_cpow (Or.inr ⟨by simpa using hs1, hz⟩)]
  have he : -s + 1 = 1 - s := by ring
  rw [he]
  push_cast
  field_simp
  ring

/-- Ordered zeta sum with its explicit pole correction.-/
def zetaPolePartialSum (s : ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1)

/-- The pole-corrected approximations differ by a finite Euler error.-/
theorem zetaPolePartialSum_sub (M N : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (s : ℂ) (hs1 : s ≠ 1) :
    zetaPolePartialSum s N - zetaPolePartialSum s M =
      (∑ n ∈ Ioc M N, (n : ℂ) ^ (-s)) -
        ∫ x : ℝ in (M : ℝ)..N, (x : ℂ) ^ (-s) := by
  rw [zetaPolePartialSum, zetaPolePartialSum,
    ← sum_Ioc_consecutive (fun n => (n : ℂ) ^ (-s)) (Nat.zero_le M) hMN,
    integral_cpow_neg_eq_pole_difference M N hM hMN s hs1]
  ring

/-- Sharp finite comparison of two pole-corrected ordered approximations.-/
theorem norm_zetaPolePartialSum_sub_le (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖zetaPolePartialSum s N - zetaPolePartialSum s M‖ ≤
      (‖s‖ / s.re) * ((M : ℝ) ^ (-s.re) - (N : ℝ) ^ (-s.re)) := by
  rw [zetaPolePartialSum_sub M N hM hMN s hs1]
  exact norm_sum_cpow_neg_sub_integral_Ioc_le M N hM hMN s hs

/-- A simpler bound suitable for ordered convergence.-/
theorem norm_zetaPolePartialSum_sub_le_left (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖zetaPolePartialSum s N - zetaPolePartialSum s M‖ ≤
      (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  apply (norm_zetaPolePartialSum_sub_le M N hM hMN s hs hs1).trans
  exact mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (div_nonneg (norm_nonneg _) hs.le)

/-- Pole-corrected ordered sums are Cauchy on `0 < s.re`, away from the pole.-/
theorem cauchySeq_zetaPolePartialSum (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    CauchySeq (zetaPolePartialSum s) := by
  apply (cauchySeq_shift 1).mp
  apply cauchySeq_of_le_tendsto_0'
    (fun n : ℕ => (‖s‖ / s.re) * ((n + 1 : ℕ) : ℝ) ^ (-s.re))
  · intro n m hnm
    rw [dist_comm, dist_eq_norm]
    exact norm_zetaPolePartialSum_sub_le_left (n + 1) (m + 1)
      (by omega) (by omega) s hs hs1
  · have hp : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hs).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    simpa using hp.const_mul (‖s‖ / s.re)

/-- An ordered pole-corrected limit exists throughout the positive half-plane
away from `1`, with an explicit error for every positive natural truncation.-/
theorem exists_zetaPolePartialSum_limit (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ∃ L : ℂ, Tendsto (zetaPolePartialSum s) atTop (𝓝 L) ∧
      ∀ M : ℕ, 1 ≤ M →
        ‖L - zetaPolePartialSum s M‖ ≤ (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_zetaPolePartialSum s hs hs1)
  refine ⟨L, hL, ?_⟩
  intro M hM
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  exact norm_zetaPolePartialSum_sub_le_left M N hM hMN s hs hs1

/-- Ordinary zeta sums converge to Mathlib's `riemannZeta` on its absolutely
convergent half-plane.-/
theorem tendsto_zetaPartialSum (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
  have hS := (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  have heq (N : ℕ) : (∑ n ∈ range (N + 1), 1 / (n : ℂ) ^ s) =
      ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s) := by
    have hset : range (N + 1) = insert 0 (Ioc 0 N) := by
      ext n
      simp only [mem_range, mem_insert, mem_Ioc]
      omega
    rw [hset, sum_insert (by simp)]
    simp [Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs), Complex.cpow_neg]
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  exact (hS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr heq

/-- The pole correction tends to zero to the right of `1`.-/
theorem tendsto_zetaPoleCorrection_zero (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (s - 1)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hr : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (show 0 < s.re - 1 by linarith)).comp
        tendsto_natCast_atTop_atTop
      simpa only [neg_sub, Function.comp_def] using h
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < N by exact_mod_cast (show 0 < N by omega))]
    simp
  simpa using hp.div_const (s - 1)

/-- The pole-corrected ordered approximation equals zeta in the original
absolutely convergent half-plane.-/
theorem tendsto_zetaPolePartialSum_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (zetaPolePartialSum s) atTop (𝓝 (riemannZeta s)) := by
  change Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s)) +
    (N : ℂ) ^ (1 - s) / (s - 1)) atTop (𝓝 (riemannZeta s))
  simpa only [add_zero] using
    (tendsto_zetaPartialSum s hs).add (tendsto_zetaPoleCorrection_zero s hs)

/-- Quantitative pole-corrected truncation of the actual zeta function on
`1 < s.re`.  Identification of the positive-half-plane ordered limit with
zeta outside this range requires a separate analytic-continuation argument.-/
theorem norm_riemannZeta_sub_sum_sub_pole_le (M : ℕ) (hM : 1 ≤ M)
    (s : ℂ) (hs : 1 < s.re) :
    ‖riemannZeta s - (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-s)) -
        (M : ℂ) ^ (1 - s) / (s - 1)‖ ≤
      (‖s‖ / s.re) * (M : ℝ) ^ (-s.re) := by
  have hL := tendsto_zetaPolePartialSum_riemannZeta s hs
  have hs1 : s ≠ 1 := by
    intro heq
    simp [heq] at hs
  have heq : riemannZeta s - (∑ n ∈ Ioc 0 M, (n : ℂ) ^ (-s)) -
      (M : ℂ) ^ (1 - s) / (s - 1) = riemannZeta s - zetaPolePartialSum s M := by
    unfold zetaPolePartialSum
    ring
  rw [heq]
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  exact norm_zetaPolePartialSum_sub_le_left M N hM hMN s
    (lt_trans zero_lt_one hs) hs1

end TwinPrime.Analytic
