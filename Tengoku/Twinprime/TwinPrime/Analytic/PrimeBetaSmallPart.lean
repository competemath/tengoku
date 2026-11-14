import Tengoku.Twinprime.TwinPrime.Analytic.BilinearPrimeBeta
import Tengoku.Twinprime.TwinPrime.Analytic.BilinearSmallPart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth-part identities for the prime-only beta weight

The prime-only weight is unchanged by multiplication by a positive smooth
integer, even if that integer has repeated prime factors. Combining this
fact with the exact low-divisor restriction gives a signed convolution
identity with no squarefreeness assumption.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- The prime-only von Mangoldt function strictly above the cutoff.-/
def primeMangoldtHigh (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if U < n ∧ n.Prime then vonMangoldt n else 0, by simp⟩

@[simp] theorem primeMangoldtHigh_apply (U n : ℕ) :
    primeMangoldtHigh U n = if U < n ∧ n.Prime then vonMangoldt n else 0 := rfl

theorem primeVaughanBeta_eq_primeMangoldtHigh_mul_zeta (U : ℕ) :
    primeVaughanBeta U = primeMangoldtHigh U * ζ := by
  ext n
  rw [primeVaughanBeta_apply, coe_mul_zeta_apply]
  rfl

theorem moebius_mul_primeVaughanBeta (U : ℕ) :
    (μ : ArithmeticFunction ℝ) * primeVaughanBeta U = primeMangoldtHigh U := by
  rw [primeVaughanBeta_eq_primeMangoldtHigh_mul_zeta]
  calc
    _ = primeMangoldtHigh U * ((μ : ArithmeticFunction ℝ) * ζ) := by ring
    _ = _ := by rw [coe_moebius_mul_coe_zeta, mul_one]

/-- A smooth factor adds no prime divisor above the cutoff. The other
factor is arbitrary and may share primes with the smooth factor.-/
theorem primeVaughanBeta_mul_smooth (U a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U) :
    primeVaughanBeta U (a * b) = primeVaughanBeta U b := by
  rw [primeVaughanBeta_apply, primeVaughanBeta_apply]
  symm
  apply sum_subset
  · intro p hp
    exact Nat.mem_divisors.mpr
      ⟨dvd_mul_of_dvd_right (Nat.dvd_of_mem_divisors hp) a, (Nat.mul_pos ha hb).ne'⟩
  intro p hp hpnot
  by_cases h : U < p ∧ p.Prime
  · exfalso
    have hpa : ¬p ∣ a := fun hpa => (not_lt_of_ge (hsmooth p h.2 hpa)) h.1
    have hpb := (h.2.dvd_or_dvd (Nat.dvd_of_mem_divisors hp)).resolve_left hpa
    exact hpnot (Nat.mem_divisors.mpr ⟨hpb, hb.ne'⟩)
  · simp [h]

/-- The entire dependence on the smooth factor is the signed truncated
Möbius divisor sum. Prime multiplicities in either factor are allowed.-/
theorem moebiusLow_mul_primeBeta_smooth_rough (U a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusLow U * primeVaughanBeta U) (a * b) =
      truncatedMoebiusSum U a * primeVaughanBeta U b := by
  rw [moebiusLow_mul_apply_mul_rough U a b ha hb hrough,
    truncatedMoebiusSum, sum_mul]
  apply sum_congr rfl
  intro d hd
  have hda := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
  have hdpos := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
  have hquot := Nat.div_dvd_of_dvd hda
  rw [primeVaughanBeta_mul_smooth U (a / d) b
    (Nat.div_pos (Nat.le_of_dvd ha hda) hdpos) hb
    (fun p hp hpd => hsmooth p hp (hpd.trans hquot))]

/-- Exact prime-only coefficient on a positive smooth-times-rough input.
The smooth part need not be squarefree or bounded by the cutoff.-/
theorem primeVaughanBilinear_eq_primeMangoldtHigh_sub_of_smooth_rough
    (U a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusHigh U * primeVaughanBeta U) (a * b) =
      primeMangoldtHigh U (a * b) - truncatedMoebiusSum U a * primeVaughanBeta U b := by
  have hsum := congrArg
    (fun f : ArithmeticFunction ℝ => (f * primeVaughanBeta U) (a * b))
    (cutoffLow_add_cutoffHigh (μ : ArithmeticFunction ℝ) U)
  change ((moebiusLow U + moebiusHigh U) * primeVaughanBeta U) (a * b) = _ at hsum
  rw [add_mul, ArithmeticFunction.add_apply, moebius_mul_primeVaughanBeta,
    moebiusLow_mul_primeBeta_smooth_rough U a b ha hb hsmooth hrough] at hsum
  linarith

/-- The prime-only weight counts each large prime once, independently of
its exponent.-/
theorem primeVaughanBeta_eq_sum_primeFactors (U b : ℕ) :
    primeVaughanBeta U b =
      ∑ p ∈ b.primeFactors, if U < p then Real.log p else 0 := by
  rw [primeVaughanBeta_apply, Nat.primeFactors_eq_to_filter_divisors_prime, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp [hp]

theorem primeVaughanBeta_eq_sum_log_of_rough (U b : ℕ)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    primeVaughanBeta U b = ∑ p ∈ b.primeFactors, Real.log p := by
  rw [primeVaughanBeta_eq_sum_primeFactors]
  apply sum_congr rfl
  intro p hp
  rw [ite_eq_left (hrough p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))]

/-- A nontrivial smooth factor prevents the entire input from being a prime
strictly above the cutoff.-/
theorem primeMangoldtHigh_mul_smooth_eq_zero (U a b : ℕ) (ha : 1 < a)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U) :
    primeMangoldtHigh U (a * b) = 0 := by
  rw [primeMangoldtHigh_apply]
  by_cases h : U < a * b ∧ (a * b).Prime
  · obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt ha)
    have hpn : p = a * b :=
      (Nat.prime_dvd_prime_iff_eq hp h.2).mp (dvd_mul_of_dvd_left hpa b)
    have hpU := hsmooth p hp hpa
    exact False.elim ((not_lt_of_ge (hpn ▸ hpU)) h.1)
  · simp [h]

theorem primeVaughanBilinear_eq_neg_mul_of_nontrivial_smooth_rough
    (U a b : ℕ) (ha : 1 < a) (hb : 0 < b)
    (hsmooth : ∀ p, Nat.Prime p → p ∣ a → p ≤ U)
    (hrough : ∀ p, Nat.Prime p → p ∣ b → U < p) :
    (moebiusHigh U * primeVaughanBeta U) (a * b) =
      -truncatedMoebiusSum U a * primeVaughanBeta U b := by
  rw [primeVaughanBilinear_eq_primeMangoldtHigh_sub_of_smooth_rough
      U a b (lt_trans Nat.zero_lt_one ha) hb hsmooth hrough,
    primeMangoldtHigh_mul_smooth_eq_zero U a b ha hsmooth]
  ring

end TwinPrime.Analytic
