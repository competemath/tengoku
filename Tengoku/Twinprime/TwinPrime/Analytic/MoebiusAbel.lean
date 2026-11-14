import Tengoku.Twinprime.TwinPrime.Analytic.PartialSummation
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusSmoothing
import Tengoku.Twinprime.TwinPrime.Analytic.CutoffLogarithms
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative ordinary partial summation

This file turns cancellation of ordinary cumulative coefficient sums into
quantitative tails for their reciprocal-weighted sums. The estimates are
generic in the coefficient sequence; applications to Möbius do not assume
that the limiting constant has already been identified.
-/

noncomputable section

open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

def coefficientSum (c : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, c n

def reciprocalCoefficientSum (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, c n / n

/-- Abel summation retaining the ordinary cumulative sums at both endpoints.-/
theorem abel_cumulative_Ioc (a b : ℕ) (hab : a ≤ b) (w c : ℕ → ℝ) :
    (∑ n ∈ Ioc a b, w n * c n) =
      w b * coefficientSum c b - w a * coefficientSum c a -
      ∑ t ∈ Ico a b, (w (t + 1) - w t) * coefficientSum c t := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hc : coefficientSum c (b + 1) = coefficientSum c b + c (b + 1) :=
      sum_Ioc_succ_top (Nat.zero_le b) c
    rw [sum_Ioc_succ_top hab (fun n => w n * c n), hc,
      sum_Ico_succ_top hab (fun t => (w (t + 1) - w t) * coefficientSum c t), ih]
    ring

/-- The exact reciprocal-weight tail in terms of ordinary cumulative sums.-/
theorem reciprocalCoefficientSum_sub_eq (c : ℕ → ℝ) (a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    reciprocalCoefficientSum c b - reciprocalCoefficientSum c a =
      coefficientSum c b / b - coefficientSum c a / a +
      ∑ t ∈ Ico a b, coefficientSum c t / ((t : ℝ) * (t + 1)) := by
  have hsum := sum_Ioc_consecutive (fun n => c n / (n : ℝ)) (Nat.zero_le a) hab
  have habell := abel_cumulative_Ioc a b hab (fun n => 1 / (n : ℝ)) c
  have hterm :
      (∑ t ∈ Ico a b, (1 / ((t + 1 : ℕ) : ℝ) - 1 / (t : ℝ)) * coefficientSum c t) =
      -(∑ t ∈ Ico a b, coefficientSum c t / ((t : ℝ) * (t + 1))) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro t ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (ha.trans (mem_Ico.mp ht).1)
    push_cast
    field_simp
    ring
  have heq : (∑ n ∈ Ioc a b, c n / (n : ℝ)) =
      coefficientSum c b / b - coefficientSum c a / a +
      ∑ t ∈ Ico a b, coefficientSum c t / ((t : ℝ) * (t + 1)) := by
    rw [hterm] at habell
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm, sub_neg_eq_add] using habell
  unfold reciprocalCoefficientSum
  rw [← hsum, add_sub_cancel_left, heq]

private theorem inverse_log_power_difference {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2 * a) :
    (b - a) / (32 * a ^ 6) ≤ 1 / a ^ 5 - 1 / b ^ 5 := by
  have hb0 : 0 < b := ha.trans_le hab
  have hden : a * b ^ 5 ≤ 32 * a ^ 6 := by
    calc
      _ ≤ a * (2 * a) ^ 5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0.le hb 5) ha.le
      _ = _ := by ring
  have hdiff : a ^ 4 * (b - a) ≤ b ^ 5 - a ^ 5 := by
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le hab 4) hb0.le
    nlinarith
  calc
    _ ≤ (b - a) / (a * b ^ 5) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (by positivity) hden
    _ = (a ^ 4 * (b - a)) / (a ^ 5 * b ^ 5) := by field_simp
    _ ≤ (b ^ 5 - a ^ 5) / (a ^ 5 * b ^ 5) :=
      div_le_div_of_nonneg_right hdiff (by positivity)
    _ = _ := by field_simp

/-- A telescoping majorant for the reciprocal-logarithm kernel.-/
theorem reciprocal_log_six_kernel_le {x : ℝ} (hx : 2 ≤ x) :
    1 / ((x + 1) * (Real.log x) ^ 6) ≤
      32 * (1 / (Real.log x) ^ 5 - 1 / (Real.log (x + 1)) ^ 5) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogle : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hlogtwo : Real.log (x + 1) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ (2 : ℕ)) := Real.log_le_log hx1 (by nlinarith [sq_nonneg (x - 2)])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hinc : 1 / (x + 1) ≤ Real.log (x + 1) - Real.log x := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx0)
    rw [Real.log_div hx1.ne' hx0.ne'] at h
    convert h using 1
    field_simp
    ring
  have hpow := inverse_log_power_difference hlog hlogle hlogtwo
  calc
    _ = (1 / (x + 1)) / (Real.log x) ^ 6 := by rw [div_div]
    _ ≤ (Real.log (x + 1) - Real.log x) / (Real.log x) ^ 6 :=
      div_le_div_of_nonneg_right hinc (by positivity)
    _ = 32 * ((Real.log (x + 1) - Real.log x) / (32 * (Real.log x) ^ 6)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)

theorem sum_reciprocal_log_six_kernel_le (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Ico a b, 1 / (((n : ℝ) + 1) * (Real.log n) ^ 6)) ≤
      32 / (Real.log a) ^ 5 := by
  calc
    _ ≤ ∑ n ∈ Ico a b,
        32 * (1 / (Real.log n) ^ 5 - 1 / (Real.log (n + 1)) ^ 5) := by
      apply sum_le_sum
      intro n hn
      exact reciprocal_log_six_kernel_le (by exact_mod_cast ha.trans (mem_Ico.mp hn).1)
    _ = 32 * (1 / (Real.log a) ^ 5 - 1 / (Real.log b) ^ 5) := by
      rw [← mul_sum]
      congr 1
      have h := sum_Ico_sub (fun n : ℕ => 1 / (Real.log n) ^ 5) hab
      have hh := congrArg Neg.neg h
      rw [← sum_neg_distrib] at hh
      simpa only [neg_sub, Nat.cast_add, Nat.cast_one] using hh
    _ ≤ _ := by
      have hb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
      have hp : 0 ≤ 1 / (Real.log b) ^ 5 := by positivity
      simp only [div_eq_mul_inv, one_mul] at hp ⊢
      linarith

/-- Quantitative ordinary cancellation gives an explicit normalized tail.-/
theorem reciprocalCoefficientSum_tail_le_log_six (c : ℕ → ℝ) (a b : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ t ∈ Icc a b,
      |coefficientSum c t| ≤ K * t / (Real.log t) ^ 6) :
    |reciprocalCoefficientSum c b - reciprocalCoefficientSum c a| ≤
      2 * K / (Real.log a) ^ 6 + 32 * K / (Real.log a) ^ 5 := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hbd (t : ℕ) (ht : t ∈ Icc a b) :
      |coefficientSum c t / t| ≤ K / (Real.log a) ^ 6 := by
    have htpos : (0 : ℝ) < t := hapos.trans_le (by exact_mod_cast (mem_Icc.mp ht).1)
    calc
      _ = |coefficientSum c t| / t := by rw [abs_div, abs_of_pos htpos]
      _ ≤ (K * t / (Real.log t) ^ 6) / t :=
        div_le_div_of_nonneg_right (hM t ht) htpos.le
      _ = K / (Real.log t) ^ 6 := by field_simp
      _ ≤ K / (Real.log a) ^ 6 := by
        exact div_le_div_of_nonneg_left hK (pow_pos hloga 6)
          (pow_le_pow_left₀ hloga.le
            (Real.log_le_log hapos (by exact_mod_cast (mem_Icc.mp ht).1)) 6)
  have hmid :
      |∑ t ∈ Ico a b, coefficientSum c t / ((t : ℝ) * (t + 1))| ≤
        32 * K / (Real.log a) ^ 5 := by
    calc
      _ ≤ ∑ t ∈ Ico a b, |coefficientSum c t / ((t : ℝ) * (t + 1))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Ico a b, K * (1 / (((t : ℝ) + 1) * (Real.log t) ^ 6)) := by
        apply sum_le_sum
        intro t ht
        have htpos : (0 : ℝ) < t := hapos.trans_le (by exact_mod_cast (mem_Ico.mp ht).1)
        have hden : 0 < (t : ℝ) * (t + 1) := mul_pos htpos (by linarith)
        rw [abs_div, abs_of_pos hden]
        calc
          _ ≤ (K * t / (Real.log t) ^ 6) / ((t : ℝ) * (t + 1)) :=
            div_le_div_of_nonneg_right (hM t (mem_Icc.mpr
              ⟨(mem_Ico.mp ht).1, (mem_Ico.mp ht).2.le⟩)) hden.le
          _ = _ := by field_simp
      _ = K * ∑ t ∈ Ico a b, 1 / (((t : ℝ) + 1) * (Real.log t) ^ 6) :=
        (mul_sum _ _ _).symm
      _ ≤ K * (32 / (Real.log a) ^ 5) :=
        mul_le_mul_of_nonneg_left (sum_reciprocal_log_six_kernel_le a b ha hab) hK
      _ = _ := by ring
  rw [reciprocalCoefficientSum_sub_eq c a b (by omega) hab]
  have hh := abs_add_le (coefficientSum c b / b - coefficientSum c a / a)
    (∑ t ∈ Ico a b, coefficientSum c t / ((t : ℝ) * (t + 1)))
  have hh' := abs_sub (coefficientSum c b / b) (coefficientSum c a / a)
  have hb := hbd b (mem_Icc.mpr ⟨hab, le_rfl⟩)
  have ha' := hbd a (mem_Icc.mpr ⟨le_rfl, hab⟩)
  simp only [mul_div_assoc] at hmid ⊢
  linarith

/-- A single fifth-power logarithmic denominator suffices uniformly from two onward.-/
theorem reciprocalCoefficientSum_tail_le_log_five (c : ℕ → ℝ) (a b : ℕ)
    (ha : 2 ≤ a) (hab : a ≤ b) (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ t ∈ Icc a b,
      |coefficientSum c t| ≤ K * t / (Real.log t) ^ 6) :
    |reciprocalCoefficientSum c b - reciprocalCoefficientSum c a| ≤
      (32 + 2 / Real.log 2) * K / (Real.log a) ^ 5 := by
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogle : Real.log (2 : ℝ) ≤ Real.log a :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ha)
  have hterm : K / (Real.log a) ^ 6 ≤ (K / Real.log 2) / (Real.log a) ^ 5 := by
    calc
      _ = (K / Real.log a) / (Real.log a) ^ 5 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left hK hlog2 hlogle) (by positivity)
  have h := reciprocalCoefficientSum_tail_le_log_six c a b ha hab K hK hM
  calc
    _ ≤ 2 * K / (Real.log a) ^ 6 + 32 * K / (Real.log a) ^ 5 := h
    _ ≤ 2 * ((K / Real.log 2) / (Real.log a) ^ 5) +
        32 * K / (Real.log a) ^ 5 := by
      simp only [mul_div_assoc] at *
      linarith
    _ = _ := by ring

/-- Ordinary logarithmic cancellation implies convergence and an explicit tail rate.
The conclusion is ordered partial-sum convergence, not unconditional summability.-/
theorem exists_reciprocalCoefficientSum_limit_of_log_six (c : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop,
      |coefficientSum c t| ≤ K * t / (Real.log t) ^ 6) :
    ∃ L : ℝ, Tendsto (reciprocalCoefficientSum c) atTop (𝓝 L) ∧
      ∀ᶠ a : ℕ in atTop,
        |reciprocalCoefficientSum c a - L| ≤
          (32 + 2 / Real.log 2) * K / (Real.log a) ^ 5 := by
  let E : ℕ → ℝ := fun a => (32 + 2 / Real.log 2) * K / (Real.log a) ^ 5
  have hE : Tendsto E atTop (𝓝 0) := by
    have hl : Tendsto (fun a : ℕ => Real.log (a : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hi := hl.inv_tendsto_atTop.pow 5
    have h := hi.const_mul ((32 + 2 / Real.log 2) * K)
    simpa [E, div_eq_mul_inv, inv_pow] using h
  rcases eventually_atTop.mp hM with ⟨N, hN⟩
  have htail (a b : ℕ) (ha : max 2 N ≤ a) (hab : a ≤ b) :
      |reciprocalCoefficientSum c b - reciprocalCoefficientSum c a| ≤ E a := by
    apply reciprocalCoefficientSum_tail_le_log_five c a b ((le_max_left _ _).trans ha) hab K hK
    intro t ht
    exact hN t ((le_max_right _ _).trans (ha.trans (mem_Icc.mp ht).1))
  have hc : CauchySeq (reciprocalCoefficientSum c) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    rcases eventually_atTop.mp (hE.eventually (gt_mem_nhds hε)) with ⟨J, hJ⟩
    refine ⟨max (max 2 N) J, fun n hn => ?_⟩
    rw [Real.dist_eq]
    exact (htail _ _ (le_max_left _ _) hn).trans_lt (hJ _ (le_max_right _ _))
  rcases cauchySeq_tendsto_of_complete hc with ⟨L, hL⟩
  refine ⟨L, hL, eventually_atTop.mpr ⟨max 2 N, fun a ha => ?_⟩⟩
  have hlim := (hL.sub_const (reciprocalCoefficientSum c a)).abs
  have hb : ∀ᶠ b : ℕ in atTop,
      |reciprocalCoefficientSum c b - reciprocalCoefficientSum c a| ≤ E a :=
    eventually_atTop.mpr ⟨a, fun b hab => htail a b ha hab⟩
  have h := le_of_tendsto hlim hb
  simpa only [abs_sub_comm] using h

/-- The ordinary Mertens partial sum, with positive integer indices.-/
def mertensSum (N : ℕ) : ℝ := coefficientSum (fun n => (μ n : ℝ)) N

@[simp] theorem reciprocalCoefficientSum_moebius (N : ℕ) :
    reciprocalCoefficientSum (fun n => (μ n : ℝ)) N = normalizedMoebiusSum N := rfl

/-- A classical ordinary Mertens bound gives a limiting normalized Möbius sum.
Its value is deliberately not identified by cancellation alone in this theorem.-/
theorem exists_normalizedMoebiusSum_limit_of_mertens_log_six (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    ∃ L : ℝ, Tendsto normalizedMoebiusSum atTop (𝓝 L) ∧
      ∀ᶠ a : ℕ in atTop,
        |normalizedMoebiusSum a - L| ≤
          (32 + 2 / Real.log 2) * K / (Real.log a) ^ 5 := by
  exact exists_reciprocalCoefficientSum_limit_of_log_six (fun n => (μ n : ℝ)) K hK hM

/-- Once the ordinary limiting constant is known, the same explicit tail holds
with that constant.-/
theorem reciprocalCoefficientSum_sub_limit_le_log_five (c : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop,
      |coefficientSum c t| ≤ K * t / (Real.log t) ^ 6)
    (L : ℝ) (hL : Tendsto (reciprocalCoefficientSum c) atTop (𝓝 L)) :
    ∀ᶠ a : ℕ in atTop,
      |reciprocalCoefficientSum c a - L| ≤
        (32 + 2 / Real.log 2) * K / (Real.log a) ^ 5 := by
  rcases exists_reciprocalCoefficientSum_limit_of_log_six c K hK hM with ⟨L', hL', htail⟩
  have heq : L' = L := tendsto_nhds_unique hL' hL
  simpa only [heq] using htail

/-- A fifth-power logarithmic tail supplies the square-logarithmic decay
needed by the subsequent finite convolution transfer.-/
theorem tendsto_mul_log_sq_of_abs_le_log_five (F : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ᶠ n : ℕ in atTop, |F n| ≤ C / (Real.log n) ^ 5) :
    Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => 4 * C / (Real.log n) ^ 3) atTop (𝓝 0) := by
    have h := (hl.inv_tendsto_atTop.pow 3).const_mul (4 * C)
    simpa [div_eq_mul_inv, inv_pow] using h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with n
    exact abs_nonneg _
  · filter_upwards [hF, eventually_ge_atTop 2] with n hn hn2
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hnpos : (0 : ℝ) < n := by linarith
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hlogle : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
      calc
        _ ≤ Real.log ((n : ℝ) ^ (2 : ℕ)) :=
          Real.log_le_log (by linarith) (by nlinarith [sq_nonneg ((n : ℝ) - 2)])
        _ = _ := by rw [Real.log_pow]; norm_num
    dsimp only [Function.comp_def]
    calc
      _ = |F n| * (Real.log (n + 1)) ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Real.log ((n : ℝ) + 1)))]
      _ ≤ (C / (Real.log n) ^ 5) * (2 * Real.log n) ^ 2 :=
        mul_le_mul hn (pow_le_pow_left₀ hlog1 hlogle 2)
          (sq_nonneg _) (div_nonneg hC (by positivity))
      _ = _ := by field_simp; ring

/-- Ordinary Mertens cancellation and identification of the normalized limit
at zero imply the stronger log-squared cancellation used by the smoothing bridge.-/
theorem tendsto_normalizedMoebiusSum_mul_log_sq_of_mertens_log_six
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6)
    (hzero : Tendsto normalizedMoebiusSum atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => normalizedMoebiusSum n * (Real.log (n + 1)) ^ 2)
      atTop (𝓝 0) := by
  apply tendsto_mul_log_sq_of_abs_le_log_five normalizedMoebiusSum
    ((32 + 2 / Real.log 2) * K) (by positivity)
  have h := reciprocalCoefficientSum_sub_limit_le_log_five
    (fun n => (μ n : ℝ)) K hK hM 0 hzero
  simpa only [reciprocalCoefficientSum_moebius, sub_zero] using h

/-- The ordinary logarithmic moment. Its limiting constant is independent data
until a boundary-value or elementary normalization argument identifies it.-/
def moebiusLogMoment (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, normalizedMoebius n * Real.log n

/-- Exact finite smoothing identity with the original real endpoint retained.-/
theorem smoothedMoebiusSum_eq_log_mul_sub_moment {x : ℝ} (hx : 0 < x) :
    smoothedMoebiusSum x =
      Real.log x * normalizedMoebiusSum ⌊x⌋₊ - moebiusLogMoment ⌊x⌋₊ := by
  unfold smoothedMoebiusSum normalizedMoebiusSum moebiusLogMoment
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
  rw [Real.log_div hx.ne' hnpos.ne']
  ring

/-- The integer logarithmic decay controls the exact real smoothing endpoint.-/
theorem tendsto_log_mul_floor_of_mul_log_sq (F : ℕ → ℝ)
    (hF : Tendsto (fun n : ℕ => F n * (Real.log (n + 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun x : ℝ => Real.log x * F ⌊x⌋₊) atTop (𝓝 0) := by
  have h := (tendsto_mul_log_of_mul_log_sq_tendsto_zero F hF).abs.comp
    (tendsto_nat_floor_atTop (α := ℝ))
  simp only [abs_zero] at h
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · filter_upwards with x
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogN : 0 ≤ Real.log ((⌊x⌋₊ : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) ⌊x⌋₊; linarith)
    dsimp only [Function.comp_def]
    rw [abs_mul, abs_of_nonneg hlogx, abs_mul, abs_of_nonneg hlogN, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hx0 (Nat.lt_floor_add_one x).le) (abs_nonneg _)

/-- Once the ordinary logarithmic moment has its classical constant `-1`,
the real-endpoint smoothed normalized Möbius sum converges to `1`.-/
theorem tendsto_smoothedMoebiusSum_of_ordinary_inputs
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6)
    (hzero : Tendsto normalizedMoebiusSum atTop (𝓝 0))
    (hmoment : Tendsto moebiusLogMoment atTop (𝓝 (-1))) :
    Tendsto smoothedMoebiusSum atTop (𝓝 1) := by
  have hfirst := tendsto_log_mul_floor_of_mul_log_sq normalizedMoebiusSum
    (tendsto_normalizedMoebiusSum_mul_log_sq_of_mertens_log_six K hK hM hzero)
  have hsecond := hmoment.comp (tendsto_nat_floor_atTop (α := ℝ))
  have h := hfirst.sub hsecond
  norm_num only [zero_sub, neg_neg] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (smoothedMoebiusSum_eq_log_mul_sub_moment (by linarith : 0 < x)).symm

end TwinPrime.Analytic
