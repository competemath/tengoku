import Tengoku.Twinprime.TwinPrime.Analytic.TruncatedMangoldt
import Tengoku.Twinprime.TwinPrime.Analytic.Vaughan
import Tengoku.Twinprime.TwinPrime.Correlation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact fixed-shift Vaughan correlation

The four terms are finite sums defined independently of twin-prime membership.
`typeITerm` and `bilinearTerm` use Dirichlet convolution, whose explicit divisor
formulas and coefficient support are proved in `Vaughan.lean`.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- `A_U(X)`, the mixed correlation.-/
def mixedCorrelation (U X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X), truncatedMangoldt U n * vonMangoldt (n + 2)

/-- `H_U(X)`, the logarithmic Type I correction.-/
def logarithmicCorrection (U X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X), vonMangoldt (n + 2) *
    (Real.log ((n : ℝ) / U) * truncatedMoebiusSum U n)

/-- `I_{U,V}(X)`. The coefficient vanishes beyond `UV`.-/
def typeITerm (U V X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X), vonMangoldt (n + 2) *
    (vaughanCoefficient U V * ζ) n

/-- `B_{U,V}(X)`, retaining the Möbius sign and the fixed shift 2.-/
def bilinearTerm (U V X : ℕ) : ℝ :=
  ∑ n ∈ Ioc X (2 * X), vonMangoldt (n + 2) *
    (moebiusHigh U * vaughanBeta V) n

def typeICorrection (U V X : ℕ) : ℝ := logarithmicCorrection U X - typeITerm U V X

/-- A supported divisor sum can be restricted to its fixed modulus range.-/
theorem convolution_zeta_eq_supported_sum (f : ArithmeticFunction ℝ) (L n : ℕ)
    (hn : 0 < n) (hf : ∀ q, L < q → f q = 0) :
    (f * ζ) n = ∑ q ∈ range (L + 1) with q ∣ n, f q := by
  rw [coe_mul_zeta_apply]
  symm
  apply Finset.sum_subset
  · intro q hq
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hq).2, hn.ne'⟩
  · intro q hq hnot
    apply hf q
    have hqdvd := (Nat.mem_divisors.mp hq).1
    by_contra h
    exact hnot (mem_filter.mpr ⟨mem_range.mpr (by omega), hqdvd⟩)

/-- The Type I term uses only moduli at most `UV`, exactly as in (D).-/
theorem typeITerm_eq_progressions (U V X : ℕ) :
    typeITerm U V X = ∑ q ∈ range (U * V + 1), vaughanCoefficient U V q *
      ∑ n ∈ Ioc X (2 * X) with q ∣ n, vonMangoldt (n + 2) := by
  unfold typeITerm
  have heq : ∀ n ∈ Ioc X (2 * X),
      (vaughanCoefficient U V * ζ) n =
        ∑ q ∈ range (U * V + 1) with q ∣ n, vaughanCoefficient U V q := by
    intro n hn
    exact convolution_zeta_eq_supported_sum _ _ n (by have := (mem_Ioc.mp hn).1; omega)
      (vaughanCoefficient_eq_zero_of_lt U V)
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  calc
    _ = ∑ n ∈ Ioc X (2 * X), ∑ q ∈ range (U * V + 1),
        if q ∣ n then vonMangoldt (n + 2) * vaughanCoefficient U V q else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [heq n hn, sum_filter, mul_sum]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp [mul_comm]

/-- The mixed correlation uses only moduli at most `U`, with the residue class
of the shifted von Mangoldt input equal to `2 mod d`.-/
theorem mixedCorrelation_eq_progressions (U X : ℕ) :
    mixedCorrelation U X = ∑ d ∈ range (U + 1), (μ d : ℝ) *
      Real.log ((U : ℝ) / d) *
        ∑ n ∈ Ioc X (2 * X) with d ∣ n, vonMangoldt (n + 2) := by
  unfold mixedCorrelation
  simp_rw [Finset.sum_filter, Finset.mul_sum]
  calc
    _ = ∑ n ∈ Ioc X (2 * X), ∑ d ∈ range (U + 1),
        if d ∣ n then (μ d : ℝ) * Real.log ((U : ℝ) / d) * vonMangoldt (n + 2)
          else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [truncatedMangoldt_eq_moduli U n (by have := (mem_Ioc.mp hn).1; omega),
        sum_filter, sum_mul]
      apply sum_congr rfl
      intro d _
      split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro n _
      split_ifs <;> simp

/-- Identity (D). Every summation input is positive and exceeds `V`.-/
theorem correlation_decomposition (U V X : ℕ) (hU : 0 < U) (hV : V ≤ X) :
    W2 X = mixedCorrelation U X + typeICorrection U V X + bilinearTerm U V X := by
  unfold W2 mixedCorrelation typeICorrection logarithmicCorrection typeITerm bilinearTerm
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnX := (Finset.mem_Ioc.mp hn).1
  have h := vaughanIdentity_apply_of_lt U V n (lt_of_le_of_lt hV hnX)
  rw [moebiusLow_mul_log_apply, truncatedMoebiusLog_eq U n hU (by omega)] at h
  rw [h]
  ring

end TwinPrime.Analytic
