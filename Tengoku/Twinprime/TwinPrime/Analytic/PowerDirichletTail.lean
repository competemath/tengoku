import Tengoku.Twinprime.TwinPrime.Analytic.CharacterDirichletTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered Dirichlet tails from power-bounded partial sums

Finite Abel summation transfers a power bound for the cumulative coefficients
to quantitative ordered tails. The resulting convergence is convergence of
the finite initial sums, without any assertion of unconditional summability.
-/

noncomputable section

open Finset MeasureTheory Filter
open scoped Interval Topology

namespace TwinPrime.Analytic

/-- A power weight on the left endpoint is absorbed in the real exponent
of the derivative integral.
@isnad1 id=le.4h4v.s7.c09acdf66e25 from=translated src=- shape=a26c36fb vocab=363b6b69
-/
theorem rpow_mul_norm_cpow_neg_sub_le (α : ℝ) (hα : 0 ≤ α)
    (s : ℂ) (hs : α < s.re) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a ^ α * ‖(b : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤
      (‖s‖ / (s.re - α)) * (a ^ (α - s.re) - b ^ (α - s.re)) := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (Complex.ne_zero_of_re_pos (hα.trans_lt hs))
  have haα : 0 ≤ a ^ α := Real.rpow_nonneg ha.le _
  have hd (x : ℝ) (hx : a ≤ x) :
      HasDerivAt (fun y : ℝ => ((a ^ α : ℝ) : ℂ) * (y : ℂ) ^ (-s))
        (((a ^ α : ℝ) : ℂ) * ((-s) * (x : ℂ) ^ (-s - 1))) x :=
    (hasDerivAt_ofReal_cpow_const (ha.trans_le hx).ne' hs0).const_mul _
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact ha.not_ge h.1
  have hi : IntervalIntegrable (fun x : ℝ => ‖s‖ * x ^ (α - s.re - 1)) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr hz)).const_mul ‖s‖
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (show ContinuousOn (fun y : ℝ => ((a ^ α : ℝ) : ℂ) * (y : ℂ) ^ (-s))
        (Set.Icc a b) from fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
    (show DifferentiableOn ℝ (fun y : ℝ => ((a ^ α : ℝ) : ℂ) * (y : ℂ) ^ (-s))
        (Set.Ioo a b) from fun x hx => (hd x hx.1.le).differentiableAt.differentiableWithinAt)
    (B := fun x : ℝ => ‖s‖ * x ^ (α - s.re - 1))
    (Eventually.of_forall (fun x hx => by
      rw [(hd x hx.1.le).deriv, norm_mul, norm_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg haα,
        Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      calc
        _ ≤ x ^ α * (‖s‖ * x ^ (-s.re - 1)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha.le hx.1.le hα)
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (ha.trans hx.1).le _))
        _ = ‖s‖ * x ^ (α - s.re - 1) := by
          rw [mul_left_comm, ← Real.rpow_add (ha.trans hx.1)]
          congr 2
          ring)) hi
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg haα] at hbound
  apply hbound.trans_eq
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, hz⟩)]
  have he : α - s.re - 1 + 1 = α - s.re := by ring
  rw [he]
  field_simp [ne_of_lt (sub_neg.mpr hs), (sub_pos.mpr hs).ne']
  ring

/-- Finite Abel summation when prefixes anchored at `M` have a power bound.
@isnad1 id=le.6h6v.s7.ad5bf73ff593 from=translated src=- shape=49913426 vocab=c2809dbd
-/
theorem norm_sum_Ioc_cpow_mul_le_of_anchored_power_sums (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (α : ℝ) (hα : 0 ≤ α)
    (s : ℂ) (hs : α < s.re) (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t ∈ Icc M N, ‖∑ n ∈ Ioc M t, a n‖ ≤ C * (t : ℝ) ^ α) :
    ‖∑ n ∈ Ioc M N, (n : ℂ) ^ (-s) * a n‖ ≤
      C * (M : ℝ) ^ (α - s.re) * (1 + ‖s‖ / (s.re - α)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hN0 := hM0.trans_le hMN'
  have hratio : 0 ≤ ‖s‖ / (s.re - α) := by positivity
  have hvar : (∑ t ∈ Ico M N, (t : ℝ) ^ α *
      ‖((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖) ≤
      (‖s‖ / (s.re - α)) *
        ((M : ℝ) ^ (α - s.re) - (N : ℝ) ^ (α - s.re)) := by
    calc
      _ ≤ ∑ t ∈ Ico M N, (‖s‖ / (s.re - α)) *
          ((t : ℝ) ^ (α - s.re) - ((t + 1 : ℕ) : ℝ) ^ (α - s.re)) := by
        apply sum_le_sum
        intro t ht
        have ht0 : (0 : ℝ) < t := hM0.trans_le (by exact_mod_cast (mem_Ico.mp ht).1)
        simpa only [Complex.ofReal_natCast] using rpow_mul_norm_cpow_neg_sub_le α hα s hs
          ht0 (show (t : ℝ) ≤ (t + 1 : ℕ) by exact_mod_cast Nat.le_succ t)
      _ = _ := by
        rw [← mul_sum]
        congr 1
        simpa only [neg_sub_neg] using
          (sum_Ico_sub (fun t : ℕ => -(t : ℝ) ^ (α - s.re)) hMN)
  rw [discrete_abel_Ioc_complex M N hMN (fun n => (n : ℂ) ^ (-s)) a]
  calc
    _ ≤ ‖(N : ℂ) ^ (-s) * (∑ n ∈ Ioc M N, a n)‖ +
        ‖∑ t ∈ Ico M N,
          (((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)) *
            (∑ n ∈ Ioc M t, a n)‖ := norm_sub_le _ _
    _ ≤ C * (N : ℝ) ^ (α - s.re) +
        C * ∑ t ∈ Ico M N, (t : ℝ) ^ α *
          ‖((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖ := by
      apply add_le_add
      · rw [norm_mul, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hN0, Complex.neg_re]
        calc
          _ ≤ (N : ℝ) ^ (-s.re) * (C * (N : ℝ) ^ α) :=
            mul_le_mul_of_nonneg_left (hA N (mem_Icc.mpr ⟨hMN, le_rfl⟩)) (by positivity)
          _ = _ := by
            rw [mul_left_comm, ← Real.rpow_add hN0]
            congr 2
            ring
      · apply (norm_sum_le _ _).trans
        rw [mul_sum]
        apply sum_le_sum
        intro t ht
        rw [norm_mul]
        calc
          _ ≤ ‖((t + 1 : ℕ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖ *
              (C * (t : ℝ) ^ α) := mul_le_mul_of_nonneg_left
                (hA t (mem_Icc.mpr ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩)) (norm_nonneg _)
          _ = _ := by ring
    _ ≤ C * (N : ℝ) ^ (α - s.re) +
        C * ((‖s‖ / (s.re - α)) *
          ((M : ℝ) ^ (α - s.re) - (N : ℝ) ^ (α - s.re))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar hC)
    _ ≤ _ := by
      have hpow := Real.rpow_le_rpow_of_nonpos hM0 hMN' (by linarith : α - s.re ≤ 0)
      have hNpow := Real.rpow_nonneg (Nat.cast_nonneg N) (α - s.re)
      nlinarith [mul_nonneg hratio hNpow, mul_le_mul_of_nonneg_left hpow hC]

/-- An ordinary cumulative power bound gives finite tails, with factor two
for changing the anchor of a partial sum.
@isnad1 id=le.6h6v.s7.e8cedc457835 from=translated src=- shape=05b04280 vocab=7df9dcce
-/
theorem norm_sum_Ioc_cpow_mul_le_of_power_partial_sums (M N : ℕ)
    (hM : 1 ≤ M) (hMN : M ≤ N) (α : ℝ) (hα : 0 ≤ α)
    (s : ℂ) (hs : α < s.re) (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α) :
    ‖∑ n ∈ Ioc M N, (n : ℂ) ^ (-s) * a n‖ ≤
      (2 * C) * (M : ℝ) ^ (α - s.re) * (1 + ‖s‖ / (s.re - α)) := by
  apply norm_sum_Ioc_cpow_mul_le_of_anchored_power_sums M N hM hMN α hα s hs a
    (2 * C) (by positivity)
  intro t ht
  have hMt := (mem_Icc.mp ht).1
  have hsum := sum_Ioc_consecutive a (Nat.zero_le M) hMt
  have heq : (∑ n ∈ Ioc M t, a n) = (∑ n ∈ Ioc 0 t, a n) - ∑ n ∈ Ioc 0 M, a n := by
    rw [← hsum]
    ring
  rw [heq]
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg M)
    (show (M : ℝ) ≤ (t : ℝ) by exact_mod_cast hMt) hα
  have hn := norm_sub_le (∑ n ∈ Ioc 0 t, a n) (∑ n ∈ Ioc 0 M, a n)
  nlinarith [hA t, hA M, mul_le_mul_of_nonneg_left hp hC]

/-- Ordered positive-index Dirichlet partial sums.-/
def powerDirichletPartialSum (a : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 N, (n : ℂ) ^ (-s) * a n

/--
@isnad1 id=eq.1h4v.s6.54f7fb8917c5 from=translated src=- shape=0e5648c9 vocab=18edcec1
-/
theorem powerDirichletPartialSum_sub (a : ℕ → ℂ) (s : ℂ)
    {M N : ℕ} (hMN : M ≤ N) :
    powerDirichletPartialSum a s N - powerDirichletPartialSum a s M =
      ∑ n ∈ Ioc M N, (n : ℂ) ^ (-s) * a n := by
  have h := sum_Ioc_consecutive (fun n => (n : ℂ) ^ (-s) * a n) (Nat.zero_le M) hMN
  unfold powerDirichletPartialSum
  rw [← h]
  ring

/--
@isnad1 id=cauchyse.4h4v.s6.2ef08fdd0991 from=translated src=- shape=17f69692 vocab=4aea6fd8
-/
theorem cauchySeq_powerDirichletPartialSum (α : ℝ) (hα : 0 ≤ α)
    (s : ℂ) (hs : α < s.re) (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α) :
    CauchySeq (powerDirichletPartialSum a s) := by
  apply (cauchySeq_shift 1).mp
  apply cauchySeq_of_le_tendsto_0'
    (fun n : ℕ => (2 * C) * ((n + 1 : ℕ) : ℝ) ^ (α - s.re) *
      (1 + ‖s‖ / (s.re - α)))
  · intro n m hnm
    rw [dist_comm, dist_eq_norm, powerDirichletPartialSum_sub a s (by omega)]
    exact norm_sum_Ioc_cpow_mul_le_of_power_partial_sums (n + 1) (m + 1)
      (by omega) (by omega) α hα s hs a C hC hA
  · have hp : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (α - s.re))
        atTop (𝓝 0) := by
      have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      simpa only [neg_sub, Function.comp_def] using ht
    simpa using (hp.const_mul (2 * C)).mul_const (1 + ‖s‖ / (s.re - α))

/-- The ordered limit exists and obeys the same explicit tail estimate.
@isnad1 id=ex.4h4v.s7.88f54ad188af from=translated src=- shape=832a1a4a vocab=5a74ddfb
-/
theorem exists_powerDirichletPartialSum_limit (α : ℝ) (hα : 0 ≤ α)
    (s : ℂ) (hs : α < s.re) (a : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ t : ℕ, ‖∑ n ∈ Ioc 0 t, a n‖ ≤ C * (t : ℝ) ^ α) :
    ∃ L : ℂ, Tendsto (powerDirichletPartialSum a s) atTop (𝓝 L) ∧
      ∀ M : ℕ, 1 ≤ M → ‖L - powerDirichletPartialSum a s M‖ ≤
        (2 * C) * (M : ℝ) ^ (α - s.re) * (1 + ‖s‖ / (s.re - α)) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_powerDirichletPartialSum α hα s hs a C hC hA)
  refine ⟨L, hL, ?_⟩
  intro M hM
  apply le_of_tendsto ((hL.sub tendsto_const_nhds).norm)
  filter_upwards [eventually_ge_atTop M] with N hMN
  rw [powerDirichletPartialSum_sub a s hMN]
  exact norm_sum_Ioc_cpow_mul_le_of_power_partial_sums M N hM hMN α hα s hs a C hC hA

end TwinPrime.Analytic
