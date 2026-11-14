import Tengoku
import Tengoku.Twinprime.TwinPrime.Sieve.Fundamental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplicative divisor sums and Rankin's trick

* `sum_divisors_eq_prod_one_add` : for multiplicative `h` and squarefree `P`,
  `∑_{d ∣ P} h d = ∏_{p ∣ P} (1 + h p)`.
* `sum_divisors_filter_ge_le` (Rankin, tail) : for `λ ≥ 1` and nonnegative multiplicative `h`,
  `∑_{d ∣ P, ω d ≥ m+1} h d ≤ λ^{-(m+1)} ∏_{p ∣ P} (1 + λ h p)`.
* `sum_divisors_filter_le_le` (Rankin, head) :
  `∑_{d ∣ P, ω d ≤ m} h d ≤ λ^m ∏_{p ∣ P} (1 + h p / λ)`.
* `prod_one_add_le_exp_sum`, `prod_one_sub_ge_exp` : elementary exponential bounds for products.
-/

noncomputable section

open Finset Real Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

namespace TwinPrime.Sieve

/-- `c^{ω d}` as an arithmetic function (`0` at `0`).-/
def powOmega (c : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else c ^ (ω d), by simp⟩

theorem powOmega_apply {c : ℝ} {d : ℕ} (hd : d ≠ 0) : powOmega c d = c ^ (ω d) := by
  show (if d = 0 then (0 : ℝ) else c ^ (ω d)) = _
  rw [ite_eq_right hd]

theorem powOmega_isMultiplicative (c : ℝ) : (powOmega c).IsMultiplicative := by
  refine ⟨by rw [powOmega_apply one_ne_zero, cardDistinctFactors_one, pow_zero], ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [powOmega, hm]
  by_cases hn : n = 0
  · simp [powOmega, hn]
  rw [powOmega_apply (mul_ne_zero hm hn), powOmega_apply hm, powOmega_apply hn,
    cardDistinctFactors_mul hmn, pow_add]

/-- For multiplicative `h` and squarefree `P`: `∑_{d ∣ P} h d = ∏_{p ∣ P} (1 + h p)`.-/
theorem sum_divisors_eq_prod_one_add (h : ArithmeticFunction ℝ) (hh : h.IsMultiplicative)
    {P : ℕ} (hP : Squarefree P) :
    ∑ d ∈ P.divisors, h d = ∏ p ∈ P.primeFactors, (1 + h p) := by
  have hmul : (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) h).IsMultiplicative :=
    isMultiplicative_moebius.intCast.pmul hh
  have hid := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree _ hmul hP
  have hleft : ∀ d ∈ P.divisors,
      (μ d : ℝ) * (ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) h) d = h d := by
    intro d hd
    have hdsq : Squarefree d := hP.squarefree_of_dvd (dvd_of_mem_divisors hd)
    rw [pmul_apply, intCoe_apply, ← mul_assoc]
    have hμ : ((μ d : ℝ)) * (μ d : ℝ) = 1 := by
      have := moebius_sq_eq_one_of_squarefree hdsq
      rw [sq] at this
      exact_mod_cast this
    rw [hμ, one_mul]
  rw [← sum_congr rfl hleft, ← hid]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [pmul_apply, intCoe_apply, moebius_apply_prime hpp]
  push_cast
  ring

/-- `∏_{i ∈ s} (1 + a i) ≤ exp (∑_{i ∈ s} a i)` for `a ≥ 0`.-/
theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  apply prod_le_prod
  · intro i hi; linarith [ha i hi]
  · intro i _; linarith [Real.add_one_le_exp (a i)]

/-- `exp (-3t) ≤ 1 - t` for `0 ≤ t ≤ 2/3`.-/
theorem exp_neg_three_mul_le_one_sub {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 2 / 3) :
    Real.exp (-(3 * t)) ≤ 1 - t := by
  have h1' : 0 < 1 - t := by linarith
  have key : 1 / (1 - t) ≤ Real.exp (t / (1 - t)) := by
    have := Real.add_one_le_exp (t / (1 - t))
    have e : t / (1 - t) + 1 = 1 / (1 - t) := by field_simp; ring
    linarith
  have h2 : Real.exp (-(t / (1 - t))) ≤ 1 - t := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) h1', ← one_div]
    exact key
  refine le_trans ?_ h2
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff, div_le_iff₀ h1']
  nlinarith

/-- `∏_{i ∈ s} (1 - t i) ≥ exp (-3 ∑ t i)` for `0 ≤ t i ≤ 2/3`.-/
theorem prod_one_sub_ge_exp {ι : Type*} (s : Finset ι) (t : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ t i)
    (h1 : ∀ i ∈ s, t i ≤ 2 / 3) :
    Real.exp (-(3 * ∑ i ∈ s, t i)) ≤ ∏ i ∈ s, (1 - t i) := by
  rw [mul_sum, ← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod
  · intro i _; exact (Real.exp_pos _).le
  · intro i hi; exact exp_neg_three_mul_le_one_sub (h0 i hi) (h1 i hi)

/-- **Rankin's trick (tail)**.-/
theorem sum_divisors_filter_ge_le (h : ArithmeticFunction ℝ) (hh : h.IsMultiplicative)
    {P : ℕ} (hP : Squarefree P) (h0 : ∀ d ∈ P.divisors, 0 ≤ h d)
    {lam : ℝ} (hlam : 1 ≤ lam) (m : ℕ) :
    ∑ d ∈ P.divisors with m + 1 ≤ ω d, h d ≤
      (lam ^ (m + 1))⁻¹ * ∏ p ∈ P.primeFactors, (1 + lam * h p) := by
  have hmul : (ArithmeticFunction.pmul h (powOmega lam)).IsMultiplicative :=
    hh.pmul (powOmega_isMultiplicative lam)
  have hid := sum_divisors_eq_prod_one_add _ hmul hP
  have hlampos : 0 < lam := by linarith
  calc ∑ d ∈ P.divisors with m + 1 ≤ ω d, h d
      ≤ ∑ d ∈ P.divisors with m + 1 ≤ ω d, (lam ^ (m + 1))⁻¹ * (h d * lam ^ (ω d)) := by
        apply sum_le_sum
        intro d hd
        rw [mem_filter] at hd
        have hhd := h0 d hd.1
        have hpow : lam ^ (m + 1) ≤ lam ^ (ω d) := pow_le_pow_right₀ hlam hd.2
        have e : (lam ^ (m + 1))⁻¹ * (h d * lam ^ (ω d)) = h d * (lam ^ (ω d) / lam ^ (m + 1)) := by
          ring
        rw [e]
        apply le_mul_of_one_le_right hhd
        rw [one_le_div (by positivity)]
        exact hpow
    _ ≤ ∑ d ∈ P.divisors, (lam ^ (m + 1))⁻¹ * (h d * lam ^ (ω d)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro d hd _
        have := h0 d hd
        positivity
    _ = (lam ^ (m + 1))⁻¹ * ∑ d ∈ P.divisors, (ArithmeticFunction.pmul h (powOmega lam)) d := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d hd
        rw [pmul_apply, powOmega_apply (Nat.pos_of_mem_divisors hd).ne']
    _ = (lam ^ (m + 1))⁻¹ * ∏ p ∈ P.primeFactors, (1 + lam * h p) := by
        rw [hid]
        congr 1
        apply prod_congr rfl
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        rw [pmul_apply, powOmega_apply hpp.ne_zero, cardDistinctFactors_apply_prime hpp, pow_one,
          mul_comm]

/-- **Rankin's trick (head)**.-/
theorem sum_divisors_filter_le_le (h : ArithmeticFunction ℝ) (hh : h.IsMultiplicative)
    {P : ℕ} (hP : Squarefree P) (h0 : ∀ d ∈ P.divisors, 0 ≤ h d)
    {lam : ℝ} (hlam : 1 ≤ lam) (m : ℕ) :
    ∑ d ∈ P.divisors with ω d ≤ m, h d ≤ lam ^ m * ∏ p ∈ P.primeFactors, (1 + h p / lam) := by
  have hmul : (ArithmeticFunction.pmul h (powOmega lam⁻¹)).IsMultiplicative :=
    hh.pmul (powOmega_isMultiplicative lam⁻¹)
  have hid := sum_divisors_eq_prod_one_add _ hmul hP
  have hlampos : 0 < lam := by linarith
  calc ∑ d ∈ P.divisors with ω d ≤ m, h d
      ≤ ∑ d ∈ P.divisors with ω d ≤ m, lam ^ m * (h d * lam⁻¹ ^ (ω d)) := by
        apply sum_le_sum
        intro d hd
        rw [mem_filter] at hd
        have hhd := h0 d hd.1
        have hpow : lam ^ (ω d) ≤ lam ^ m := pow_le_pow_right₀ hlam hd.2
        have e : lam ^ m * (h d * lam⁻¹ ^ (ω d)) = h d * (lam ^ m / lam ^ (ω d)) := by
          rw [inv_pow]; field_simp
        rw [e]
        apply le_mul_of_one_le_right hhd
        rw [one_le_div (by positivity)]
        exact hpow
    _ ≤ ∑ d ∈ P.divisors, lam ^ m * (h d * lam⁻¹ ^ (ω d)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro d hd _
        have := h0 d hd
        positivity
    _ = lam ^ m * ∑ d ∈ P.divisors, (ArithmeticFunction.pmul h (powOmega lam⁻¹)) d := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d hd
        rw [pmul_apply, powOmega_apply (Nat.pos_of_mem_divisors hd).ne']
    _ = lam ^ m * ∏ p ∈ P.primeFactors, (1 + h p / lam) := by
        rw [hid]
        congr 1
        apply prod_congr rfl
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        rw [pmul_apply, powOmega_apply hpp.ne_zero, cardDistinctFactors_apply_prime hpp, pow_one,
          div_eq_mul_inv]

end TwinPrime.Sieve
