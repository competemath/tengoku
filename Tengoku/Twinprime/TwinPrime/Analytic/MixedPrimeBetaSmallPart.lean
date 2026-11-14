import Tengoku.Twinprime.TwinPrime.Analytic.PrimeBetaSmallPart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth-part identities with distinct Möbius and beta cutoffs

For U ≤ W, factor the input as a positive W-smooth part times a positive
W-rough part. The prime-beta cutoff is W, but the truncated Möbius coefficient
still has cutoff U. A prime in the interval (U,W] therefore contributes a
negative rough-prime weight, rather than the cancellation at equal cutoffs.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem moebiusLow_mul_primeBeta_mixed_smooth_rough (U W a b : ℕ)
    (hUW : U ≤ W) (ha : 0 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ W)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → W < p) :
    (moebiusLow U * primeVaughanBeta W) (a * b) =
      truncatedMoebiusSum U a * primeVaughanBeta W b := by
  rw [moebiusLow_mul_apply_mul_rough U a b ha hb
      (fun p hp hpb => hUW.trans_lt (hrough p hp hpb)),
    truncatedMoebiusSum, sum_mul]
  apply sum_congr rfl
  intro d hd
  have hda := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
  have hdpos := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
  have hquot := Nat.div_dvd_of_dvd hda
  rw [primeVaughanBeta_mul_smooth W (a / d) b
    (Nat.div_pos (Nat.le_of_dvd ha hda) hdpos) hb
    (fun p hp hpd => hsmooth p hp (hpd.trans hquot))]

/-- The Möbius cutoff stays U even when smoothness and the prime-beta
cutoff use W. Neither factor is required to be squarefree.-/
theorem primeVaughanBilinear_eq_primeMangoldtHigh_sub_of_mixed_smooth_rough
    (U W a b : ℕ) (hUW : U ≤ W) (ha : 0 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ W)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → W < p) :
    (moebiusHigh U * primeVaughanBeta W) (a * b) =
      primeMangoldtHigh W (a * b) - truncatedMoebiusSum U a * primeVaughanBeta W b := by
  have hsum := congrArg
    (fun f : ArithmeticFunction ℝ => (f * primeVaughanBeta W) (a * b))
    (cutoffLow_add_cutoffHigh (μ : ArithmeticFunction ℝ) U)
  change ((moebiusLow U + moebiusHigh U) * primeVaughanBeta W) (a * b) = _ at hsum
  rw [add_mul, ArithmeticFunction.add_apply, moebius_mul_primeVaughanBeta,
    moebiusLow_mul_primeBeta_mixed_smooth_rough U W a b hUW ha hb hsmooth hrough] at hsum
  linarith

theorem primeVaughanBilinear_eq_neg_mul_of_nontrivial_mixed_smooth_rough
    (U W a b : ℕ) (hUW : U ≤ W) (ha : 1 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ W)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → W < p) :
    (moebiusHigh U * primeVaughanBeta W) (a * b) =
      -truncatedMoebiusSum U a * primeVaughanBeta W b := by
  rw [primeVaughanBilinear_eq_primeMangoldtHigh_sub_of_mixed_smooth_rough
      U W a b hUW (lt_trans Nat.zero_lt_one ha) hb hsmooth hrough,
    primeMangoldtHigh_mul_smooth_eq_zero W a b ha hsmooth]
  ring

theorem truncatedMoebiusSum_prime_of_cutoff_lt (U p : ℕ) (hU : 1 ≤ U)
    (hp : Nat.Prime p) (hUp : U < p) : truncatedMoebiusSum U p = 1 := by
  rw [truncatedMoebiusSum, hp.divisors, sum_filter]
  simp [hU, Nat.not_le.mpr hUp, hp.ne_one.symm]

/-- A prime between the two cutoffs gives a negative prime-beta coefficient.
In particular raising the beta cutoff does not replace m_U with m_W.-/
theorem primeVaughanBilinear_eq_neg_primeBeta_of_middle_prime (U W p b : ℕ)
    (hU : 1 ≤ U) (hp : Nat.Prime p) (hUp : U < p) (hpW : p ≤ W)
    (hb : 0 < b) (hrough : ∀ q, Nat.Prime q → q ∣ b → W < q) :
    (moebiusHigh U * primeVaughanBeta W) (p * b) = -primeVaughanBeta W b := by
  have hsmooth : ∀ q, Nat.Prime q → q ∣ p → q ≤ W := by
    intro q hq hqp
    exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp) ▸ hpW
  rw [primeVaughanBilinear_eq_neg_mul_of_nontrivial_mixed_smooth_rough
      U W p b (hUp.le.trans hpW) hp.one_lt hb hsmooth hrough,
    truncatedMoebiusSum_prime_of_cutoff_lt U p hU hp hUp]
  ring

theorem primeVaughanBilinear_nonpos_of_middle_prime (U W p b : ℕ)
    (hU : 1 ≤ U) (hp : Nat.Prime p) (hUp : U < p) (hpW : p ≤ W)
    (hb : 0 < b) (hrough : ∀ q, Nat.Prime q → q ∣ b → W < q) :
    (moebiusHigh U * primeVaughanBeta W) (p * b) ≤ 0 := by
  rw [primeVaughanBilinear_eq_neg_primeBeta_of_middle_prime
    U W p b hU hp hUp hpW hb hrough]
  exact neg_nonpos.mpr (primeVaughanBeta_nonneg W b)

end TwinPrime.Analytic
