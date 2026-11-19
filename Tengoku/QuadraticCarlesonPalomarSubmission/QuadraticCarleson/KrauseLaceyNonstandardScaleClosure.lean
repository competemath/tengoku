import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyNonstandardLocalInterpolation
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyNonstandardSourceMaximal
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyScaleSummation
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyPStoppingRecursion
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.NonstandardThresholdAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Summation of the actual nonstandard good collection

This file performs the scale-parameter optimization left after the concrete
nonstandard physical `L²` and local-average pairing estimates.  The numerical
weight used below is the source weight

`((s + 1)^2 2^(-s))^(1/q)`.

Its polynomial factor is *inside* the `q`th root.  Consequently it is bounded
by a universal constant times `2^(-s/(5q))`, and summing costs only one Holder
conjugate.  This is the point of the threshold used in the source argument.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

noncomputable section

/-- The dimensionless scale weight before taking the Holder-conjugate root.-/
def nonstandardScaleWeight (s : ℕ) : ℝ :=
  ((s + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (-(s : ℝ))

/--
@isnad1 id=lt.0h1v.s3.8227245f5e24 from=translated src=- shape=b9369acb vocab=d2bf50b8
-/
theorem nonstandardScaleWeight_pos (s : ℕ) :
    0 < nonstandardScaleWeight s := by
  unfold nonstandardScaleWeight
  positivity

/-- A deliberately roomy universal polynomial/exponential comparison.
@isnad1 id=le.0h1v.s6.d8d52613e5ce from=translated src=- shape=f0082a9e vocab=ad3e4bb6
-/
theorem sq_succ_le_sixtyFour_mul_rpow_four_fifths (s : ℕ) :
    (((s + 1 : ℕ) : ℝ) ^ 2) ≤
      64 * (2 : ℝ) ^ ((4 : ℝ) * s / 5) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      by_cases hs : s ≤ 5
      · have hsq : (((s + 1 : ℕ) : ℝ) ^ 2) ≤ 36 := by
          norm_num at hs ⊢
          interval_cases s <;> norm_num
        have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ ((4 : ℝ) * s / 5) := by
          exact Real.one_le_rpow (by norm_num) (by positivity)
        nlinarith
      · have hs6 : 6 ≤ s := by omega
        let t := s - 5
        have htlt : t < s := by dsimp [t]; omega
        have ht1 : 1 ≤ t := by dsimp [t]; omega
        have hi := ih t htlt
        have hnat : s = t + 5 := by dsimp [t]; omega
        have hlin : ((s + 1 : ℕ) : ℝ) ≤ 4 * (((t + 1 : ℕ) : ℝ)) := by
          exact_mod_cast (show s + 1 ≤ 4 * (t + 1) by omega)
        have hsq : (((s + 1 : ℕ) : ℝ) ^ 2) ≤
            16 * (((t + 1 : ℕ) : ℝ) ^ 2) := by nlinarith
        calc
          (((s + 1 : ℕ) : ℝ) ^ 2) ≤
              16 * (((t + 1 : ℕ) : ℝ) ^ 2) := hsq
          _ ≤ 16 * (64 * (2 : ℝ) ^ ((4 : ℝ) * t / 5)) := by gcongr
          _ = 64 * (2 : ℝ) ^ ((4 : ℝ) * s / 5) := by
            rw [hnat]
            rw [show (4 : ℝ) * (↑(t + 5) : ℝ) / 5 =
              (4 : ℝ) * t / 5 + 4 by push_cast; ring]
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            norm_num
            ring

/--
@isnad1 id=le.0h1v.s5.07956c1acc0f from=translated src=- shape=69feeb86 vocab=9181ca1c
-/
theorem nonstandardScaleWeight_le (s : ℕ) :
    nonstandardScaleWeight s ≤ 64 * (2 : ℝ) ^ (-(s : ℝ) / 5) := by
  have h := sq_succ_le_sixtyFour_mul_rpow_four_fifths s
  have hmul := mul_le_mul_of_nonneg_right h
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(s : ℝ)))
  unfold nonstandardScaleWeight
  calc
    (((s + 1 : ℕ) : ℝ) ^ 2) * (2 : ℝ) ^ (-(s : ℝ)) ≤
        (64 * (2 : ℝ) ^ ((4 : ℝ) * s / 5)) *
          (2 : ℝ) ^ (-(s : ℝ)) := hmul
    _ = 64 * (2 : ℝ) ^ (-(s : ℝ) / 5) := by
      rw [mul_assoc]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- The source weight is controlled by the concrete ratio already summed in
`KrauseLaceyScaleSummation`, with a universal factor eight.
@isnad1 id=le.1h2v.s6.4ba01df23ecf from=translated src=- shape=54e886ff vocab=772f2088
-/
theorem nonstandardScaleWeight_rpow_le_scaleDecayRatio
    {q : ℝ} (hq : 2 ≤ q) (s : ℕ) :
    nonstandardScaleWeight s ^ (1 / q) ≤
      8 * scaleDecayRatio q ^ s := by
  have hq0 : 0 < q := by linarith
  have hpow := Real.rpow_le_rpow
    (nonstandardScaleWeight_pos s).le (nonstandardScaleWeight_le s)
      (by positivity : 0 ≤ (1 : ℝ) / q)
  have hexp : (1 : ℝ) / q ≤ 1 / 2 := by
    exact (div_le_div_iff_of_pos_left one_pos hq0 (by norm_num)).mpr hq
  have h64 : (64 : ℝ) ^ (1 / q) ≤ 8 := by
    calc
      (64 : ℝ) ^ (1 / q) ≤ (64 : ℝ) ^ (1 / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 8 := by norm_num [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
  calc
    nonstandardScaleWeight s ^ (1 / q) ≤
        (64 * (2 : ℝ) ^ (-(s : ℝ) / 5)) ^ (1 / q) := hpow
    _ = (64 : ℝ) ^ (1 / q) *
        (2 : ℝ) ^ ((-(s : ℝ) / 5) * (1 / q)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 8 * (2 : ℝ) ^ ((-(s : ℝ) / 5) * (1 / q)) := by
      gcongr
    _ = 8 * scaleDecayRatio q ^ s := by
      unfold scaleDecayRatio
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
      congr 2
      field_simp

/--
@isnad1 id=le.1h2v.s6.1bc69e7ec41d from=translated src=- shape=cad91257 vocab=a9553776
-/
theorem finite_sum_nonstandardScaleWeight_rpow_le
    {q : ℝ} (hq : 2 ≤ q) (N : ℕ) :
    (∑ s ∈ Finset.range N, nonstandardScaleWeight s ^ (1 / q)) ≤ 160 * q := by
  calc
    _ ≤ ∑ s ∈ Finset.range N, 8 * scaleDecayRatio q ^ s := by
      exact Finset.sum_le_sum fun s _ ↦ nonstandardScaleWeight_rpow_le_scaleDecayRatio hq s
    _ = 8 * ∑ s ∈ Finset.range N, scaleDecayRatio q ^ s := by
      rw [Finset.mul_sum]
    _ ≤ 8 * (20 * q) := by
      gcongr
      simpa only [Finset.sum_filter, Finset.mem_range, ite_eq_left] using
        finite_scaleDecayRatio_sum_le_twenty_mul_q hq N
    _ = 160 * q := by ring

/-- The source threshold.  It balances the `L²` term carrying
`sqrt (nonstandardScaleWeight s)` against the local `L¹` term.-/
def nonstandardScaleThreshold (a p : ℝ) (s : ℕ) : ℝ :=
  a * nonstandardScaleWeight s ^ (-1 / p)

/--
@isnad1 id=lt.2h3v.s5.2139a16e8b99 from=translated src=- shape=b4e35a70 vocab=c6e2e426
-/
theorem nonstandardScaleThreshold_pos {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (s : ℕ) :
    0 < nonstandardScaleThreshold a p s := by
  unfold nonstandardScaleThreshold
  exact mul_pos ha (Real.rpow_pos_of_pos (nonstandardScaleWeight_pos s) _)

/--
@isnad1 id=eq.2h3v.s7.a8d0a7fa4ca8 from=translated src=- shape=79a030db vocab=541a47b6
-/
theorem sqrt_weight_mul_threshold_rpow
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (s : ℕ) :
    Real.sqrt (nonstandardScaleWeight s) *
        nonstandardScaleThreshold a p s ^ (1 - p / 2) =
      a ^ (1 - p / 2) * nonstandardScaleWeight s ^ ((p - 1) / p) := by
  simpa only [nonstandardScaleThreshold] using
    sqrt_mul_threshold_rpow ha (nonstandardScaleWeight_pos s) hp

/--
@isnad1 id=eq.2h3v.s6.febeedf9f7e7 from=translated src=- shape=c07388a3 vocab=c76fce98
-/
theorem threshold_rpow_one_sub
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (s : ℕ) :
    nonstandardScaleThreshold a p s ^ (1 - p) =
      a ^ (1 - p) * nonstandardScaleWeight s ^ ((p - 1) / p) := by
  simpa only [nonstandardScaleThreshold] using
    positive_threshold_rpow_one_sub ha (nonstandardScaleWeight_pos s) hp

/--
@isnad1 id=eq.1h1v.s5.f36ad725a448 from=translated src=- shape=686704cc vocab=366aacb9
-/
theorem one_div_holderConjugate_eq {p : ℝ} (hp : 1 < p) :
    1 / holderConjugate p = (p - 1) / p := by
  rw [holderConjugate]
  exact reciprocal_holder_quotient p

end

end KrauseLaceyBadScale
end QuadraticCarleson
