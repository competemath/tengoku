import Tengoku.Rankamplificationtotient.RankAmplification.DivisorSmoothTail
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Full-exponent prime Rankin sums This file extends the small-exponent estimate in `PrimeSums` to the full range needed by the paper. -/

namespace RankAmplification

open Finset MeasureTheory
open scoped Nat.Prime

noncomputable section

/-- A convenient absolute constant in the explicit prime-counting bound.-/
def primeCountingConstant : ℝ := 2 * Real.log 4 + 2

/--
@isnad1 id=lt.0h0v.s3.d473b600f2df from=translated src=- shape=ff3a10fc vocab=0e1e0279
-/
theorem primeCountingConstant_pos : 0 < primeCountingConstant := by
  rw [primeCountingConstant]
  positivity

/-- Elementary inequality used to absorb the square-root term in Chebyshev's explicit bound.
@isnad1 id=le.1h1v.s5.fdbc54ed8193 from=translated src=- shape=07dccf84 vocab=71d83edf
-/
theorem log_le_two_mul_sqrt {x : ℝ} (hx : 1 < x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (zero_lt_one.trans hx)
  have h := Real.add_one_le_exp (Real.log x / 2)
  rw [← Real.log_sqrt (zero_lt_one.trans hx).le, Real.exp_log hsqrt] at h
  calc
    Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt (zero_lt_one.trans hx).le]
      ring
    _ ≤ 2 * Real.sqrt x := by linarith

/-- Pure `x / log x` form of Mathlib's explicit Chebyshev prime-counting estimate.
@isnad1 id=le.1h1v.s5.5b57f610e12a from=translated src=- shape=b996d074 vocab=4c44f634
-/
theorem primeCounting_le_constant_mul_div {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ primeCountingConstant * x / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 (zero_lt_one.trans hx)
  have hsqrtTerm : Real.sqrt x ≤ 2 * x / Real.log x := by
    apply (le_div_iff₀ hlog).2
    calc
      Real.sqrt x * Real.log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (log_le_two_mul_sqrt hx) hsqrt.le
      _ = 2 * (Real.sqrt x * Real.sqrt x) := by ring
      _ = 2 * x := by rw [Real.mul_self_sqrt (zero_lt_one.trans hx).le]
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
        Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x :=
      Chebyshev.pi_le_log4_mul_div hx
    _ = 2 * Real.log 4 * x / Real.log x + Real.sqrt x := by
      rw [Real.log_sqrt (zero_lt_one.trans hx).le]
      field_simp
    _ ≤ 2 * Real.log 4 * x / Real.log x + 2 * x / Real.log x :=
      add_le_add_right hsqrtTerm _
    _ = primeCountingConstant * x / Real.log x := by
      rw [primeCountingConstant]
      ring

/-- Local integrability of the Abel kernel for the full Rankin prime sum.
@isnad1 id=integrab.0h2v.s6.5288cf0ea2f5 from=translated src=- shape=66a71ba0 vocab=8a565389
-/
theorem integrableOn_primeCounting_mul_rpow (R : ℝ) (δ : ℝ) :
    IntegrableOn (fun t : ℝ ↦
      (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2)) (Set.Icc 2 R) volume := by
  let c : ℕ → ℝ := Set.indicator {n : ℕ | n.Prime} (fun _ ↦ 1)
  have hg : IntegrableOn (fun t : ℝ ↦ t ^ (δ - 2)) (Set.Icc 2 R) volume := by
    refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_id.rpow_const (Or.inl ht0)).continuousWithinAt
  have h := integrableOn_mul_sum_Icc (m := 0) c (show (0 : ℝ) ≤ 2 by norm_num) hg
  convert h using 1
  funext t
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
  simp [c, Set.indicator_apply]
  ring

/-- Exact Abel-summation identity for the full prime Rankin sum.
@isnad1 id=eq.1h2v.s7.bd37096fbee5 from=translated src=- shape=13707b55 vocab=59e44018
-/
theorem primeRankinSum_eq_primeCounting_integral {R : ℕ} {δ : ℝ} (hR : 2 ≤ R) :
    primeRankinSum R δ =
      (R : ℝ) ^ (-1 + δ) * Nat.primeCounting R +
        (1 - δ) * ∫ t in (2 : ℝ)..R,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2) := by
  let c : ℕ → ℝ := Set.indicator {n : ℕ | n.Prime} (fun _ ↦ 1)
  rw [primeRankinSum, Nat.primesLE_eq_filter_Icc_zero, sum_filter]
  trans ∑ n ∈ Icc 0 R, (n : ℝ) ^ (-1 + δ) * c n
  · apply sum_congr rfl
    intro n hn
    split_ifs with hp
    · simp [c, hp]
    · simp [c, hp]
  nth_rewrite 1 [← Nat.floor_natCast (R := ℝ) R]
  rw [sum_mul_eq_sub_integral_mul₁ (f := fun t : ℝ ↦ t ^ (-1 + δ)) c
    (by simp [c, Nat.not_prime_zero]) (by simp [c, Nat.not_prime_one]) R,
    ← intervalIntegral.integral_of_le (mod_cast hR)]
  · have hsum (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
        (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
      rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Icc_zero]
      simp [c, Set.indicator_apply]
    simp_rw [hsum]
    rw [Nat.floor_natCast]
    have hderiv (t : ℝ) :
        deriv (fun u : ℝ ↦ u ^ (-1 + δ)) t =
          (-1 + δ) * t ^ (δ - 2) := by
      rw [Real.deriv_rpow_const]
      congr 2
      ring
    simp_rw [hderiv]
    have hinterm (t : ℝ) :
        (-1 + δ) * t ^ (δ - 2) * (Nat.primeCounting ⌊t⌋₊ : ℝ) =
          (-1 + δ) * ((Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2)) := by ring
    simp_rw [hinterm]
    rw [intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl <| by linarith [ht.1])).differentiableAt
  · have hint : IntegrableOn (fun t : ℝ ↦
        (-1 + δ) * t ^ (δ - 2)) (Set.Icc 2 R) := by
      refine ContinuousOn.integrableOn_Icc fun t ht ↦ ?_
      have ht0 : id t ≠ 0 := by
        simpa only [id_eq] using (show t ≠ 0 by linarith [ht.1])
      exact (continuousAt_const.mul <|
        continuousAt_id.rpow_const (Or.inl ht0)).continuousWithinAt
    convert hint using 1
    funext t
    rw [Real.deriv_rpow_const]
    congr 2
    ring

/-! ## Reduction to one elementary logarithmic integral -/

/-- The exponential-integral kernel arising from partial summation.-/
def rankinLogIntegral (δ : ℝ) (R : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..R, t ^ (δ - 1) / Real.log t

/--
@isnad1 id=interval.2h3v.s6.6808b1caa805 from=translated src=- shape=c89c4093 vocab=bf82cac4
-/
theorem intervalIntegrable_rankinLogKernel {δ a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ (δ - 1) / Real.log t) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hab] at ht
  have htpos : 0 < t := zero_lt_one.trans_le (ha.le.trans ht.1)
  have hlog : Real.log t ≠ 0 :=
    (Real.log_pos (ha.trans_le ht.1)).ne'
  exact (continuousAt_id.rpow_const (Or.inl htpos.ne')).div
    (Real.continuousAt_log htpos.ne') hlog

/--
@isnad1 id=le.1h2v.s4.f5d0cc1c37c3 from=translated src=- shape=61bdc3e7 vocab=047d3000
-/
theorem rankinLogIntegral_nonneg {δ : ℝ} {R : ℝ} (hR : 2 ≤ R) :
    0 ≤ rankinLogIntegral δ R := by
  rw [rankinLogIntegral]
  apply intervalIntegral.integral_nonneg hR
  intro t ht
  exact div_nonneg (Real.rpow_nonneg (by linarith [ht.1]) _)
    (Real.log_nonneg (by linarith [ht.1]))

/-- Abel summation and the explicit prime-counting estimate reduce the full Rankin sum to `rankinLogIntegral`.
@isnad1 id=le.2h2v.s6.f6809bb90538 from=translated src=- shape=7f5bb78c vocab=ce780581
-/
theorem primeRankinSum_le_rankinLogIntegral {R : ℕ} {δ : ℝ}
    (hR : 2 ≤ R) (hδ0 : 0 ≤ δ) :
    primeRankinSum R δ ≤ primeCountingConstant *
      ((R : ℝ) ^ δ / Real.log R + rankinLogIntegral δ R) := by
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hRone : (1 : ℝ) < R := lt_of_lt_of_le (by norm_num) hRreal
  have hRpos : 0 < (R : ℝ) := zero_lt_one.trans hRone
  have hboundaryPi : (Nat.primeCounting R : ℝ) ≤
      primeCountingConstant * R / Real.log R := by
    simpa using primeCounting_le_constant_mul_div hRone
  have hboundary : (R : ℝ) ^ (-1 + δ) * Nat.primeCounting R ≤
      primeCountingConstant * ((R : ℝ) ^ δ / Real.log R) := by
    calc
      (R : ℝ) ^ (-1 + δ) * Nat.primeCounting R ≤
          (R : ℝ) ^ (-1 + δ) *
            (primeCountingConstant * R / Real.log R) :=
        mul_le_mul_of_nonneg_left hboundaryPi (Real.rpow_nonneg hRpos.le _)
      _ = primeCountingConstant * ((R : ℝ) ^ δ / Real.log R) := by
        have hrpow : (R : ℝ) ^ (-1 + δ) * R = (R : ℝ) ^ δ := by
          calc
            (R : ℝ) ^ (-1 + δ) * R =
                (R : ℝ) ^ (-1 + δ) * (R : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
            _ = (R : ℝ) ^ ((-1 + δ) + 1) :=
              (Real.rpow_add hRpos (-1 + δ) 1).symm
            _ = (R : ℝ) ^ δ := by congr 1; ring
        rw [div_eq_mul_inv, div_eq_mul_inv, ← hrpow]
        ring
  have hleft : IntervalIntegrable (fun t : ℝ ↦
      (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2)) volume 2 R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hRreal]
    exact integrableOn_primeCounting_mul_rpow R δ
  have hright : IntervalIntegrable (fun t : ℝ ↦
      primeCountingConstant * (t ^ (δ - 1) / Real.log t)) volume 2 R :=
    (intervalIntegrable_rankinLogKernel (by norm_num) hRreal).const_mul _
  have hintegral : (∫ t in (2 : ℝ)..R,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2)) ≤
      primeCountingConstant * rankinLogIntegral δ R := by
    rw [rankinLogIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hRreal hleft hright
    intro t ht
    have htone : 1 < t := lt_of_lt_of_le (by norm_num) ht.1
    have htpos : 0 < t := zero_lt_one.trans htone
    have hpi := primeCounting_le_constant_mul_div htone
    calc
      (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2) ≤
          (primeCountingConstant * t / Real.log t) * t ^ (δ - 2) :=
        mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg htpos.le _)
      _ = primeCountingConstant * (t ^ (δ - 1) / Real.log t) := by
        have hrpow : t * t ^ (δ - 2) = t ^ (δ - 1) := by
          calc
            t * t ^ (δ - 2) = t ^ (1 : ℝ) * t ^ (δ - 2) := by
              rw [Real.rpow_one]
            _ = t ^ ((1 : ℝ) + (δ - 2)) :=
              (Real.rpow_add htpos 1 (δ - 2)).symm
            _ = t ^ (δ - 1) := by congr 1; ring
        rw [div_eq_mul_inv, div_eq_mul_inv, ← hrpow]
        ring
  have hintegral0 : 0 ≤ ∫ t in (2 : ℝ)..R,
      (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2) := by
    apply intervalIntegral.integral_nonneg hRreal
    intro t ht
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith [ht.1]) _)
  have hcoeffOne : 1 - δ ≤ 1 := by linarith
  rw [primeRankinSum_eq_primeCounting_integral hR]
  calc
    (R : ℝ) ^ (-1 + δ) * Nat.primeCounting R +
        (1 - δ) * ∫ t in (2 : ℝ)..R,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) * t ^ (δ - 2) ≤
        primeCountingConstant * ((R : ℝ) ^ δ / Real.log R) +
          primeCountingConstant * rankinLogIntegral δ R := by
      apply add_le_add hboundary
      exact (mul_le_mul hcoeffOne hintegral hintegral0 zero_le_one).trans_eq (one_mul _)
    _ = primeCountingConstant *
        ((R : ℝ) ^ δ / Real.log R + rankinLogIntegral δ R) := by ring

/-! ## The split logarithmic integral -/

/-- Derivative of the endpoint kernel used on the upper part of the split integral.
@isnad1 id=eq.1h2v.s7.6ff0aea57cc5 from=translated src=- shape=e2c0c3a6 vocab=0a4f61e2
-/
theorem deriv_rpow_div_log {δ t : ℝ} (ht : 1 < t) :
    deriv (fun x : ℝ ↦ x ^ δ / Real.log x) t =
      t ^ (δ - 1) * (δ * Real.log t - 1) / Real.log t ^ 2 := by
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hd := (Real.hasDerivAt_rpow_const (x := t) (p := δ) (Or.inl ht0)).div
    (Real.hasDerivAt_log ht0) hlog
  change deriv ((fun x : ℝ ↦ x ^ δ) / Real.log) t = _
  rw [hd.deriv]
  rw [Real.rpow_sub_one ht0]
  field_simp

/-- On a range where `δ log B ≤ 2`, the exponential weight costs only `exp 2`.
@isnad1 id=le.3h2v.s6.0b894a185cc2 from=translated src=- shape=33444d54 vocab=aa89efec
-/
theorem rankinLogIntegral_le_exp_two_loglog {δ B : ℝ}
    (hB : 2 ≤ B) (hδ0 : 0 ≤ δ) (hδB : δ * Real.log B ≤ 2) :
    rankinLogIntegral δ B ≤ Real.exp 2 *
      (Real.log (Real.log B) - Real.log (Real.log 2)) := by
  have hBone : (1 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  have hBpos : 0 < B := zero_lt_one.trans hBone
  have hBpow : B ^ δ ≤ Real.exp 2 := by
    rw [Real.rpow_def_of_pos hBpos]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hleft := intervalIntegrable_rankinLogKernel (δ := δ) (by norm_num) hB
  have hright : IntervalIntegrable (fun t : ℝ ↦
      Real.exp 2 * (t⁻¹ / Real.log t)) volume 2 B := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hB] at ht
    have htpos : 0 < t := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    exact continuousAt_const.mul <|
      (continuousAt_id.inv₀ htpos.ne').div (Real.continuousAt_log htpos.ne') hlog
  rw [rankinLogIntegral]
  calc
    (∫ t in (2 : ℝ)..B, t ^ (δ - 1) / Real.log t) ≤
        ∫ t in (2 : ℝ)..B, Real.exp 2 * (t⁻¹ / Real.log t) := by
      apply intervalIntegral.integral_mono_on hB hleft hright
      intro t ht
      have htpos : 0 < t := by linarith [ht.1]
      have hlogpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have htpow : t ^ δ ≤ Real.exp 2 :=
        (Real.rpow_le_rpow htpos.le ht.2 hδ0).trans hBpow
      have hq : 0 ≤ t⁻¹ / Real.log t := div_nonneg (inv_nonneg.mpr htpos.le) hlogpos.le
      calc
        t ^ (δ - 1) / Real.log t = t ^ δ * (t⁻¹ / Real.log t) := by
          rw [Real.rpow_sub_one htpos.ne']
          field_simp
        _ ≤ Real.exp 2 * (t⁻¹ / Real.log t) :=
          mul_le_mul_of_nonneg_right htpow hq
    _ = Real.exp 2 *
        (Real.log (Real.log B) - Real.log (Real.log 2)) := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_div_log (by norm_num) hBone]

/-- Above a point where `δ log A ≥ 2`, the logarithmic kernel is controlled by the derivative of `t^δ / log t`.
@isnad1 id=le.4h3v.s7.82d48f790b7b from=translated src=- shape=ffe33e1e vocab=bdcca873
-/
theorem rankinLogIntegral_tail_le {δ A B : ℝ}
    (hδ : 0 < δ) (hA : 1 < A) (hAB : A ≤ B)
    (hδA : 2 ≤ δ * Real.log A) :
    (∫ t in A..B, t ^ (δ - 1) / Real.log t) ≤
      2 * B ^ δ / (δ * Real.log B) := by
  let g : ℝ → ℝ := fun t ↦ t ^ δ / Real.log t
  let g' : ℝ → ℝ := fun t ↦
    t ^ (δ - 1) * (δ * Real.log t - 1) / Real.log t ^ 2
  have hleft := intervalIntegrable_rankinLogKernel (δ := δ) hA hAB
  have hg'int : IntervalIntegrable g' volume A B := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hAB] at ht
    have htone : 1 < t := hA.trans_le ht.1
    have htpos : 0 < t := zero_lt_one.trans htone
    have hlog : Real.log t ≠ 0 := (Real.log_pos htone).ne'
    have hlog2 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 hlog
    dsimp [g']
    exact ((continuousAt_id.rpow_const (Or.inl htpos.ne')).mul
      (continuousAt_const.mul (Real.continuousAt_log htpos.ne') |>.sub continuousAt_const)).div
        ((Real.continuousAt_log htpos.ne').pow 2) hlog2
  have hright : IntervalIntegrable (fun t ↦ (2 / δ) * g' t) volume A B :=
    hg'int.const_mul _
  have hmono : (∫ t in A..B, t ^ (δ - 1) / Real.log t) ≤
      ∫ t in A..B, (2 / δ) * g' t := by
    apply intervalIntegral.integral_mono_on hAB hleft hright
    intro t ht
    have htone : 1 < t := hA.trans_le ht.1
    have htpos : 0 < t := zero_lt_one.trans htone
    have hlogpos : 0 < Real.log t := Real.log_pos htone
    have hlogle : Real.log A ≤ Real.log t :=
      Real.log_le_log (zero_lt_one.trans hA) ht.1
    have hδt : 2 ≤ δ * Real.log t :=
      hδA.trans (mul_le_mul_of_nonneg_left hlogle hδ.le)
    have hpowpos : 0 < t ^ (δ - 1) := Real.rpow_pos_of_pos htpos _
    dsimp [g']
    field_simp
    nlinarith
  have hfund : (∫ t in A..B, g' t) = g B - g A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hAB] at ht
      have htone : 1 < t := hA.trans_le ht.1
      have ht0 : t ≠ 0 := (zero_lt_one.trans htone).ne'
      have hlog : Real.log t ≠ 0 := (Real.log_pos htone).ne'
      have hdiffer : DifferentiableAt ℝ (fun x : ℝ ↦ x ^ δ / Real.log x) t :=
        ((Real.hasDerivAt_rpow_const (x := t) (p := δ) (Or.inl ht0)).div
          (Real.hasDerivAt_log ht0) hlog).differentiableAt
      dsimp [g, g']
      rw [← deriv_rpow_div_log htone]
      exact hdiffer.hasDerivAt
    · exact hg'int
  have hgA : 0 ≤ g A := by
    dsimp [g]
    exact div_nonneg (Real.rpow_nonneg (zero_lt_one.trans hA).le _)
      (Real.log_pos hA).le
  have hlogB : 0 < Real.log B := Real.log_pos (hA.trans_le hAB)
  calc
    (∫ t in A..B, t ^ (δ - 1) / Real.log t) ≤
        ∫ t in A..B, (2 / δ) * g' t := hmono
    _ = (2 / δ) * (g B - g A) := by
      rw [intervalIntegral.integral_const_mul, hfund]
    _ ≤ (2 / δ) * g B := by
      apply mul_le_mul_of_nonneg_left (sub_le_self _ hgA) (by positivity)
    _ = 2 * B ^ δ / (δ * Real.log B) := by
      dsimp [g]
      field_simp

/-- Uniform bound for the logarithmic Rankin integral throughout `0 < δ ≤ 1/2`.
@isnad1 id=le.3h2v.s7.031179526931 from=translated src=- shape=6393ebdb vocab=533beb51
-/
theorem rankinLogIntegral_le_full {δ R : ℝ}
    (hR : 2 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    rankinLogIntegral δ R ≤
      Real.exp 2 * (Real.log (Real.log R) - Real.log (Real.log 2)) +
        2 * R ^ δ / (δ * Real.log R) := by
  have hRone : (1 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR
  have hlogR : 0 < Real.log R := Real.log_pos hRone
  by_cases hsmall : δ * Real.log R ≤ 2
  · exact (rankinLogIntegral_le_exp_two_loglog hR hδ.le hsmall).trans <|
      le_add_of_nonneg_right (by positivity)
  · have hlarge : 2 < δ * Real.log R := lt_of_not_ge hsmall
    let A : ℝ := Real.exp (2 / δ)
    have hfour : (4 : ℝ) ≤ 2 / δ := by
      apply (le_div_iff₀ hδ).2
      linarith
    have hlog2lt : Real.log (2 : ℝ) < 2 / δ := by
      have hlog2one : Real.log (2 : ℝ) < 1 := by
        have h := Real.log_lt_sub_one_of_pos
          (show (0 : ℝ) < 2 by norm_num) (by norm_num)
        norm_num at h ⊢
        exact h
      exact hlog2one.trans (lt_of_lt_of_le (by norm_num) hfour)
    have hA2 : (2 : ℝ) ≤ A := by
      calc
        (2 : ℝ) = Real.exp (Real.log 2) :=
          (Real.exp_log (show (0 : ℝ) < 2 by norm_num)).symm
        _ ≤ Real.exp (2 / δ) := Real.exp_le_exp.mpr hlog2lt.le
        _ = A := rfl
    have hAone : (1 : ℝ) < A := lt_of_lt_of_le (by norm_num) hA2
    have hApos : 0 < A := zero_lt_one.trans hAone
    have hlogA : Real.log A = 2 / δ := by simp [A]
    have hδA : δ * Real.log A = 2 := by
      rw [hlogA]
      field_simp
    have hAB : A ≤ R := by
      have hquot : 2 / δ < Real.log R := by
        apply (div_lt_iff₀ hδ).2
        nlinarith
      dsimp [A]
      rw [← Real.exp_log (zero_lt_one.trans hRone)]
      exact Real.exp_le_exp.mpr hquot.le
    have hlowA := rankinLogIntegral_le_exp_two_loglog hA2 hδ.le hδA.le
    have hlogAle : Real.log A ≤ Real.log R := Real.log_le_log hApos hAB
    have hloglogle : Real.log (Real.log A) ≤ Real.log (Real.log R) :=
      Real.log_le_log (Real.log_pos hAone) hlogAle
    have hlow : rankinLogIntegral δ A ≤
        Real.exp 2 * (Real.log (Real.log R) - Real.log (Real.log 2)) :=
      hlowA.trans <| mul_le_mul_of_nonneg_left
        (sub_le_sub_right hloglogle _) (Real.exp_pos 2).le
    have htail := rankinLogIntegral_tail_le hδ hAone hAB hδA.symm.le
    rw [rankinLogIntegral]
    calc
      (∫ t in (2 : ℝ)..R, t ^ (δ - 1) / Real.log t) =
          (∫ t in (2 : ℝ)..A, t ^ (δ - 1) / Real.log t) +
            ∫ t in A..R, t ^ (δ - 1) / Real.log t := by
        exact (intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_rankinLogKernel (by norm_num) hA2)
          (intervalIntegrable_rankinLogKernel hAone hAB)).symm
      _ ≤ Real.exp 2 * (Real.log (Real.log R) - Real.log (Real.log 2)) +
          2 * R ^ δ / (δ * Real.log R) := add_le_add hlow htail

/-! ## Full prime-sum bounds -/

/-- Direct explicit full-exponent estimate before harmless normalization of the two terms.
@isnad1 id=le.3h2v.s7.254c2850603d from=translated src=- shape=f3e6623a vocab=864d95a6
-/
theorem primeRankinSum_le_full_raw {R : ℕ} {δ : ℝ}
    (hR : 2 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    primeRankinSum R δ ≤ primeCountingConstant *
      ((R : ℝ) ^ δ / Real.log R +
        Real.exp 2 * (Real.log (Real.log R) - Real.log (Real.log 2)) +
        2 * (R : ℝ) ^ δ / (δ * Real.log R)) := by
  have hreduce := primeRankinSum_le_rankinLogIntegral hR hδ.le
  have hint := rankinLogIntegral_le_full
    (R := (R : ℝ)) (δ := δ) (by exact_mod_cast hR) hδ hδhalf
  apply hreduce.trans
  apply mul_le_mul_of_nonneg_left _ primeCountingConstant_pos.le
  simpa only [add_assoc] using
    add_le_add_right hint ((R : ℝ) ^ δ / Real.log R)

/-- Explicit absolute-constant error of shape `log log (3R) + R^δ / (δ log R)`.-/
def fullPrimeRankinError (R : ℕ) (δ : ℝ) : ℝ :=
  primeCountingConstant *
    (Real.exp 2 *
        (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2)) +
      3 * (R : ℝ) ^ δ / (δ * Real.log R))

/-- The desired unconditional full-exponent prime Rankin estimate.
@isnad1 id=le.3h2v.s5.4f319c00fda8 from=translated src=- shape=215e3854 vocab=41372188
-/
theorem primeRankinSum_le_full {R : ℕ} {δ : ℝ}
    (hR : 2 ≤ R) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    primeRankinSum R δ ≤ fullPrimeRankinError R δ := by
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hRone : (1 : ℝ) < R := lt_of_lt_of_le (by norm_num) hRreal
  have hRpos : 0 < (R : ℝ) := zero_lt_one.trans hRone
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hδone : δ ≤ 1 := hδhalf.trans (by norm_num)
  have hendpoint : (R : ℝ) ^ δ / Real.log R ≤
      (R : ℝ) ^ δ / (δ * Real.log R) := by
    apply (div_le_div_iff₀ hlogR (mul_pos hδ hlogR)).2
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hRpos.le _)
    exact mul_le_of_le_one_left hlogR.le hδone
  have hRle : (R : ℝ) ≤ 3 * R := by nlinarith
  have hlogle : Real.log (R : ℝ) ≤ Real.log (3 * R) :=
    Real.log_le_log hRpos hRle
  have hloglogle : Real.log (Real.log (R : ℝ)) ≤
      Real.log (Real.log (3 * R)) :=
    Real.log_le_log hlogR hlogle
  have hinside :
      (R : ℝ) ^ δ / Real.log R +
          Real.exp 2 * (Real.log (Real.log R) - Real.log (Real.log 2)) +
          2 * (R : ℝ) ^ δ / (δ * Real.log R) ≤
        Real.exp 2 *
            (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2)) +
          3 * (R : ℝ) ^ δ / (δ * Real.log R) := by
    calc
      (R : ℝ) ^ δ / Real.log R +
            Real.exp 2 * (Real.log (Real.log R) - Real.log (Real.log 2)) +
            2 * (R : ℝ) ^ δ / (δ * Real.log R) ≤
          (R : ℝ) ^ δ / (δ * Real.log R) +
            Real.exp 2 *
              (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2)) +
            2 * (R : ℝ) ^ δ / (δ * Real.log R) := by
        exact add_le_add (add_le_add hendpoint <|
          mul_le_mul_of_nonneg_left (sub_le_sub_right hloglogle _) (Real.exp_pos 2).le) le_rfl
      _ = Real.exp 2 *
            (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2)) +
          3 * (R : ℝ) ^ δ / (δ * Real.log R) := by ring
  exact (primeRankinSum_le_full_raw hR hδ hδhalf).trans <| by
    rw [fullPrimeRankinError]
    exact mul_le_mul_of_nonneg_left hinside primeCountingConstant_pos.le

/-! ## The paper's exponent and the all-range divisor tail -/

/-- At the paper's chosen exponent, `R^δ = u`.
@isnad1 id=eq.2h2v.s5.fb6a32164297 from=translated src=- shape=ef4d9491 vocab=7f1c3157
-/
theorem rankinBase_rpow_delta {X R : ℕ} (hR : 1 < R) (hu : 0 < rankinU X R) :
    (R : ℝ) ^ rankinDelta X R = rankinU X R := by
  have hRpos : 0 < (R : ℝ) := by positivity
  have hlogR : Real.log (R : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hR)).ne'
  rw [Real.rpow_def_of_pos hRpos, rankinDelta]
  have hexp : Real.log (R : ℝ) *
      (Real.log (rankinU X R) / Real.log R) = Real.log (rankinU X R) := by
    field_simp
  rw [hexp, Real.exp_log hu]

/-- Full-range prime error after substituting `R^δ = u` and `δ log R = log u`.-/
def fullULogUPrimeError (R X : ℕ) : ℝ :=
  primeCountingConstant *
    (Real.exp 2 *
        (Real.log (Real.log (3 * (R : ℝ))) - Real.log (Real.log 2)) +
      3 * rankinU X R / Real.log (rankinU X R))

/-- Unconditional `log log (3R) + u / log u` estimate throughout the paper range `1 < u ≤ √R`.
@isnad1 id=le.3h2v.s5.7ecb1a9d9792 from=translated src=- shape=20c90fe8 vocab=0ffbc1a2
-/
theorem primeRankinSum_le_full_uLogU {R X : ℕ}
    (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R) :
    primeRankinSum R (rankinDelta X R) ≤ fullULogUPrimeError R X := by
  have hR' : 1 < R := lt_of_lt_of_le (by norm_num) hR
  have hδpos : 0 < rankinDelta X R := by
    rw [rankinDelta]
    exact div_pos (Real.log_pos hu) (Real.log_pos (by exact_mod_cast hR'))
  have hδhalf : rankinDelta X R ≤ 1 / 2 :=
    rankinDelta_le_half_of_u_le_sqrt hR' (zero_lt_one.trans hu) huSqrt
  have h := primeRankinSum_le_full hR hδpos hδhalf
  have hpow := rankinBase_rpow_delta hR' (zero_lt_one.trans hu)
  have hδlog := rankinDelta_mul_log_base (H := X) hR'
  rw [fullPrimeRankinError, hpow, hδlog] at h
  simpa only [fullULogUPrimeError] using h

/-- Fixed Euler loss times the unconditional full-range prime error.-/
def fullPaperDivisorError (R X : ℕ) : ℝ :=
  divisorEulerHalfLoss * fullULogUPrimeError R X

/-- Lemma 2.5's general exponential estimate on the entire paper range `1 < u ≤ √R`; unlike `finiteDivisorWeightedSmoothCount_le_paper_error`, this theorem has no small-exponent premise.
@isnad1 id=le.4h2v.s6.d76e5506b8f4 from=translated src=- shape=d16c5389 vocab=2771f4b1
-/
theorem finiteDivisorWeightedSmoothCount_le_full_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X) := by
  have hR' : 1 < R := lt_of_lt_of_le (by norm_num) hR
  have huR : rankinU X R < R :=
    huSqrt.trans_lt (Real.sqrt_lt_self_iff.mpr (by exact_mod_cast hR'))
  have hδhalf : rankinDelta X R ≤ 1 / 2 :=
    rankinDelta_le_half_of_u_le_sqrt hR' (zero_lt_one.trans hu) huSqrt
  have hprime : primeRankinSum R (rankinDelta X R) ≤ fullULogUPrimeError R X :=
    primeRankinSum_le_full_uLogU hR hu huSqrt
  have hloss : divisorEulerLoss (1 - rankinDelta X R) ≤ divisorEulerHalfLoss :=
    divisorEulerLoss_le_half hδhalf
  have herror : divisorEulerLoss (1 - rankinDelta X R) *
      primeRankinSum R (rankinDelta X R) ≤ fullPaperDivisorError R X := by
    rw [fullPaperDivisorError]
    exact mul_le_mul hloss hprime (primeRankinSum_nonneg R (rankinDelta X R))
      divisorEulerHalfLoss_pos.le
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) +
            divisorEulerLoss (1 - rankinDelta X R) *
              primeRankinSum R (rankinDelta X R)) :=
      finiteDivisorWeightedSmoothCount_le_exp_primeRankinSum hX hR' hu.le huR
    _ ≤ (X : ℝ) * Real.exp
        (-rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.exp_le_exp.mpr (add_le_add_right herror _)

/-- Log-normalized full-range form of the general estimate (2.6).
@isnad1 id=le.4h2v.s6.83a762146279 from=translated src=- shape=9549ec05 vocab=875f1d80
-/
theorem log_divisorWeightedSmoothCount_div_le_full_paper_error {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R) :
    Real.log (finiteDivisorWeightedSmoothCount R X / X) ≤
      -rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X := by
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hbound := finiteDivisorWeightedSmoothCount_le_full_paper_error
    hX hR hu huSqrt
  have hdiv : finiteDivisorWeightedSmoothCount R X / X ≤
      Real.exp (-rankinU X R * Real.log (rankinU X R) +
        fullPaperDivisorError R X) := by
    apply (div_le_iff₀ hXreal).2
    simpa [mul_comm] using hbound
  have hdivpos : 0 < finiteDivisorWeightedSmoothCount R X / X :=
    div_pos (finiteDivisorWeightedSmoothCount_pos hX) hXreal
  simpa only [Real.log_exp] using Real.log_le_log hdivpos hdiv

/-- Clean full-range form of Lemma 2.5 under the explicit dominance inequality.
@isnad1 id=le.5h2v.s7.261657d3d016 from=translated src=- shape=5750f192 vocab=973d4ae8
-/
theorem finiteDivisorWeightedSmoothCount_le_full_half_u_log_u {R X : ℕ}
    (hX : 0 < X) (hR : 2 ≤ R) (hu : 1 < rankinU X R)
    (huSqrt : rankinU X R ≤ Real.sqrt R)
    (hdom : fullPaperDivisorError R X ≤
      rankinU X R * Real.log (rankinU X R) / 2) :
    finiteDivisorWeightedSmoothCount R X ≤
      (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
  calc
    finiteDivisorWeightedSmoothCount R X ≤
        (X : ℝ) * Real.exp
          (-rankinU X R * Real.log (rankinU X R) + fullPaperDivisorError R X) :=
      finiteDivisorWeightedSmoothCount_le_full_paper_error hX hR hu huSqrt
    _ ≤ (X : ℝ) * Real.exp
        (-(rankinU X R * Real.log (rankinU X R)) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith

end

end RankAmplification
