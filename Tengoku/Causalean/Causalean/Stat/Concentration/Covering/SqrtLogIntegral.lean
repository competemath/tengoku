module
public import Tengoku

/-!
Dudley entropy-integral evaluation for a logarithmic square-root kernel.

This file proves the elementary bound
`∫ x in ε..δ, sqrt (log (δ / x)) ≤ δ - ε` for `0 < ε ≤ δ`. The proof uses
the AM-GM inequality `sqrt t ≤ (t + 1) / 2` for `t ≥ 0` and the explicit
antiderivative of `log`.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory Set
open scoped Interval

/-- For nonnegative `t`, the square root is bounded by the arithmetic mean of
`t` and `1`.
@isnad1 id=le.1h1v.s5.697d6f8e913f from=translated src=- shape=6a2e150a vocab=aae65541
-/
lemma sqrt_le_add_one_div_two {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt t ≤ (t + 1) / 2 := by
  have hsq : 0 ≤ (Real.sqrt t - 1) ^ 2 := sq_nonneg _
  have hsqrt_sq : (Real.sqrt t) ^ 2 = t := by
    rw [Real.sq_sqrt ht]
  nlinarith [hsq, Real.sqrt_nonneg t, hsqrt_sq]

/-- On the interval `[ε, δ]`, the log-ratio kernel is nonnegative.
@isnad1 id=le.2h3v.s5.fd5bb92923bd from=translated src=- shape=bb59b703 vocab=d0c53cfa
-/
lemma log_div_nonneg_of_mem_Icc {δ ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc ε δ) :
    0 ≤ Real.log (δ / x) := by
  have hxpos : 0 < x := lt_of_lt_of_le hε hx.1
  have hratio : 1 ≤ δ / x := by
    rw [le_div_iff₀ hxpos]
    simpa using hx.2
  exact Real.log_nonneg hratio

private lemma continuousOn_sqrt_log_div_Icc {δ ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    ContinuousOn (fun x : ℝ => Real.sqrt (Real.log (δ / x))) (Set.Icc ε δ) := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  refine ContinuousOn.sqrt ?_
  refine ContinuousOn.log ?_ ?_
  · exact (continuousOn_const (c := δ)).div continuousOn_id (fun x hx => by
      linarith [hx.1])
  · intro x hx
    exact div_ne_zero (ne_of_gt hδ) (by linarith [hx.1])

/-- When ε is positive and no larger than δ, the square-root log-ratio kernel is integrable on
the interval from ε to δ with respect to Lebesgue measure.
@isnad1 id=interval.2h2v.s5.31283677c1dc from=translated src=- shape=1689287b vocab=073c6387
-/
lemma intervalIntegrable_sqrt_log_div {δ ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    IntervalIntegrable (fun x : ℝ => Real.sqrt (Real.log (δ / x))) volume ε δ := by
  have hcont : ContinuousOn (fun x : ℝ => Real.sqrt (Real.log (δ / x))) [[ε, δ]] := by
    simpa [Set.uIcc_of_le hεδ] using continuousOn_sqrt_log_div_Icc hε hεδ
  exact hcont.intervalIntegrable

private lemma continuousOn_log_div_avg_Icc {δ ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    ContinuousOn (fun x : ℝ => (Real.log (δ / x) + 1) / 2) (Set.Icc ε δ) := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  refine ((ContinuousOn.log ?_ ?_).add continuousOn_const).div_const 2
  · exact (continuousOn_const (c := δ)).div continuousOn_id (fun x hx => by
      linarith [hx.1])
  · intro x hx
    exact div_ne_zero (ne_of_gt hδ) (by linarith [hx.1])

private lemma intervalIntegrable_log_div_avg {δ ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    IntervalIntegrable (fun x : ℝ => (Real.log (δ / x) + 1) / 2) volume ε δ := by
  have hcont : ContinuousOn (fun x : ℝ => (Real.log (δ / x) + 1) / 2) [[ε, δ]] := by
    simpa [Set.uIcc_of_le hεδ] using continuousOn_log_div_avg_Icc hε hεδ
  exact hcont.intervalIntegrable

/-- When ε is positive and no larger than δ, the logarithm of the ratio δ divided by x is
interval-integrable from ε to δ with respect to Lebesgue measure.
@isnad1 id=interval.2h2v.s5.47706a6c1a14 from=translated src=- shape=80e4520f vocab=c14e1d2b
-/
lemma intervalIntegrable_log_div {δ ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ δ) :
    IntervalIntegrable (fun x : ℝ => Real.log (δ / x)) volume ε δ := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  have hcont : ContinuousOn (fun x : ℝ => Real.log (δ / x)) (Set.Icc ε δ) := by
    refine ContinuousOn.log ?_ ?_
    · exact (continuousOn_const (c := δ)).div continuousOn_id (fun x hx => by
        linarith [hx.1])
    · intro x hx
      exact div_ne_zero (ne_of_gt hδ) (by linarith [hx.1])
  have hcont' : ContinuousOn (fun x : ℝ => Real.log (δ / x)) [[ε, δ]] := by
    simpa [Set.uIcc_of_le hεδ] using hcont
  exact hcont'.intervalIntegrable

/-- Exact evaluation of the logarithmic ratio integral on `[ε, δ]`.
@isnad1 id=eq.2h2v.s6.caff863d38d8 from=translated src=- shape=9d64e840 vocab=d58a970e
-/
lemma integral_log_div_eq {δ ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    (∫ x in ε..δ, Real.log (δ / x)) =
      δ - ε - ε * Real.log (δ / ε) := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  calc
    (∫ x in ε..δ, Real.log (δ / x))
        = ∫ x in ε..δ, (Real.log δ - Real.log x) := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          have hxIcc : x ∈ Set.Icc ε δ := by
            simpa [Set.uIcc_of_le hεδ] using hx
          have hxpos : 0 < x := lt_of_lt_of_le hε hxIcc.1
          simpa using Real.log_div (ne_of_gt hδ) (ne_of_gt hxpos)
    _ = (δ - ε) * Real.log δ -
          (δ * Real.log δ - ε * Real.log ε - δ + ε) := by
          rw [intervalIntegral.integral_sub]
          · rw [intervalIntegral.integral_const]
            rw [integral_log]
            simp [smul_eq_mul]
          · exact intervalIntegrable_const
          · exact intervalIntegral.intervalIntegrable_log'
    _ = δ - ε - ε * Real.log (δ / ε) := by
          rw [Real.log_div (ne_of_gt hδ) (ne_of_gt hε)]
          ring

/-- The logarithmic ratio integral over `[ε, δ]` is at most the interval length.
@isnad1 id=le.2h2v.s6.46a4e3de06a4 from=translated src=- shape=036ee67b vocab=b0f31aa8
-/
lemma integral_log_div_le {δ ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    (∫ x in ε..δ, Real.log (δ / x)) ≤ δ - ε := by
  have hratio : 1 ≤ δ / ε := by
    rw [le_div_iff₀ hε]
    simpa using hεδ
  have hnonneg : 0 ≤ ε * Real.log (δ / ε) :=
    mul_nonneg (le_of_lt hε) (Real.log_nonneg hratio)
  rw [integral_log_div_eq hε hεδ]
  linarith

/-- **Dudley entropy-integral evaluation.** For [a positive lower limit ε](hyp:hε) that is [at most
the upper limit δ](hyp:hεδ), [the integral of `√(log(δ/x))` over `[ε,δ]` is at most `δ - ε`](goal).

Elementary (AM-GM `√t ≤ (t+1)/2` + `∫ log(δ/x) ≤ δ - ε`); no special
functions beyond `Real.log`.
@isnad1 id=le.2h2v.s6.89a46093174c from=translated src=- shape=97b94086 vocab=5646f5a0
-/
lemma sqrtLog_integral_le {δ ε : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    (∫ x in ε..δ, Real.sqrt (Real.log (δ / x))) ≤ δ - ε := by
  have hmono :
      (∫ x in ε..δ, Real.sqrt (Real.log (δ / x))) ≤
        ∫ x in ε..δ, (Real.log (δ / x) + 1) / 2 := by
    refine intervalIntegral.integral_mono_on hεδ
      (intervalIntegrable_sqrt_log_div hε hεδ)
      (intervalIntegrable_log_div_avg hε hεδ) ?_
    intro x hx
    exact sqrt_le_add_one_div_two (log_div_nonneg_of_mem_Icc hε hx)
  have hlog :
      (∫ x in ε..δ, Real.log (δ / x)) ≤ δ - ε :=
    integral_log_div_le hε hεδ
  have havg :
      (∫ x in ε..δ, (Real.log (δ / x) + 1) / 2) ≤ δ - ε := by
    have hint :
        (∫ x in ε..δ, (Real.log (δ / x) + 1) / 2) =
          ((∫ x in ε..δ, Real.log (δ / x)) + (δ - ε)) / 2 := by
      rw [intervalIntegral.integral_div]
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const]
        simp [smul_eq_mul]
      · exact intervalIntegrable_log_div hε hεδ
      · exact intervalIntegrable_const
    rw [hint]
    linarith
  calc
    (∫ x in ε..δ, Real.sqrt (Real.log (δ / x)))
        ≤ ∫ x in ε..δ, (Real.log (δ / x) + 1) / 2 := hmono
    _ ≤ δ - ε := havg

end Causalean.Stat.Concentration
