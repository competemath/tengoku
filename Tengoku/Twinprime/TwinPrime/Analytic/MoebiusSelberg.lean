import Tengoku.Seed.NumberTheory.ArithmeticFunction.VonMangoldt
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact second-order Möbius convolution algebra

The centered coefficient used in `docs/PNT_MERTENS_REDUCTION.md` is
`Λ * Λ - (Λ log) - 2c ζ`, where multiplication is Dirichlet convolution
and `Λ log` is pointwise multiplication. The identities here are finite
and unconditional. No estimate for the summatory coefficient or a
prime-to-Mertens implication is claimed in this module.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

/-- Pointwise multiplication by the real logarithm of the natural input.-/
def arithmeticLogWeight (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f.pmul ArithmeticFunction.log

@[simp] theorem arithmeticLogWeight_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticLogWeight f n = f n * Real.log n := rfl

theorem arithmeticLogWeight_mul (f g : ArithmeticFunction ℝ) :
    arithmeticLogWeight (f * g) =
      arithmeticLogWeight f * g + f * arithmeticLogWeight g := by
  ext n
  simp only [arithmeticLogWeight_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.add_apply, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hm := (Nat.mem_divisorsAntidiagonal.mp hd).1
  have h₁ : (d.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd)
  have h₂ : (d.2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd)
  rw [← hm, Nat.cast_mul, Real.log_mul h₁ h₂]
  ring

@[simp] theorem arithmeticLogWeight_neg (f : ArithmeticFunction ℝ) :
    arithmeticLogWeight (-f) = -arithmeticLogWeight f := by
  ext n
  simp

/-- The first-order identity obtained from the divisor sum for von Mangoldt.-/
theorem arithmeticLogWeight_moebius :
    arithmeticLogWeight (μ : ArithmeticFunction ℝ) =
      -((μ : ArithmeticFunction ℝ) * vonMangoldt) := by
  have hz : arithmeticLogWeight (μ : ArithmeticFunction ℝ) * ζ = -vonMangoldt := by
    ext n
    simpa only [coe_mul_zeta_apply, arithmeticLogWeight_apply,
      intCoe_apply, ArithmeticFunction.neg_apply, ArithmeticFunction.log_apply]
      using (sum_moebius_mul_log_eq (n := n))
  calc
    arithmeticLogWeight (μ : ArithmeticFunction ℝ) =
        (arithmeticLogWeight (μ : ArithmeticFunction ℝ) * ζ) * μ := by
          rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
    _ = -((μ : ArithmeticFunction ℝ) * vonMangoldt) := by
      rw [hz]
      ring

/-- The second derivative identity, with both logarithmic weights pointwise.-/
theorem arithmeticLogWeight_twice_moebius :
    arithmeticLogWeight (arithmeticLogWeight (μ : ArithmeticFunction ℝ)) =
      (μ : ArithmeticFunction ℝ) *
        (vonMangoldt * vonMangoldt - arithmeticLogWeight vonMangoldt) := by
  rw [arithmeticLogWeight_moebius, arithmeticLogWeight_neg,
    arithmeticLogWeight_mul, arithmeticLogWeight_moebius]
  ring

/-- The centered Selberg coefficient. The real constant is arbitrary here.-/
def centeredSelbergCoefficient (c : ℝ) : ArithmeticFunction ℝ :=
  vonMangoldt * vonMangoldt - arithmeticLogWeight vonMangoldt -
    (2 * c) • (ζ : ArithmeticFunction ℝ)

/-- Exact centered convolution identity, valid also at the unused index zero.-/
theorem moebius_mul_centeredSelbergCoefficient (c : ℝ) :
    (μ : ArithmeticFunction ℝ) * centeredSelbergCoefficient c =
      arithmeticLogWeight (arithmeticLogWeight (μ : ArithmeticFunction ℝ)) -
        (2 * c) • (1 : ArithmeticFunction ℝ) := by
  rw [centeredSelbergCoefficient, mul_sub, mul_smul_comm,
    coe_moebius_mul_coe_zeta, arithmeticLogWeight_twice_moebius]

/-- The same identity expressed entirely as a finite divisor-pair sum.-/
theorem moebius_mul_centeredSelbergCoefficient_apply (c : ℝ) (n : ℕ) :
    (∑ d ∈ n.divisorsAntidiagonal,
      (μ d.1 : ℝ) * centeredSelbergCoefficient c d.2) =
      (μ n : ℝ) * (Real.log n) ^ 2 - if n = 1 then 2 * c else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (moebius_mul_centeredSelbergCoefficient c)
  simpa [sub_eq_add_neg, ArithmeticFunction.one_apply,
    pow_two, mul_assoc] using h

end TwinPrime.Analytic
