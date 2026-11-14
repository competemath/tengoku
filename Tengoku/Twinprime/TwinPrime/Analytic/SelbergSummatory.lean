import Tengoku.Twinprime.TwinPrime.Analytic.Hyperbola
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusSelberg
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusAbel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real summatory forms of the centered Selberg identity

The hyperbola split is instantiated with the actual arithmetic coefficients,
including the constant at one and the overlap rectangle. These exact formulas
do not assert a bound for the centered summatory function or for Mertens.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace TwinPrime.Analytic

def mertensReal (x : ℝ) : ℝ := arithmeticSummatory (μ : ArithmeticFunction ℝ) x

def moebiusLogSqSummatory (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, (μ n : ℝ) * (Real.log n) ^ 2

def primeLogSummatory (x : ℝ) : ℝ :=
  arithmeticSummatory (arithmeticLogWeight vonMangoldt) x

def centeredSelbergSummatory (c x : ℝ) : ℝ :=
  arithmeticSummatory (centeredSelbergCoefficient c) x

theorem mertensReal_eq (x : ℝ) : mertensReal x = mertensSum ⌊x⌋₊ := rfl

theorem arithmeticSummatory_vonMangoldt (x : ℝ) :
    arithmeticSummatory vonMangoldt x = Chebyshev.psi x := rfl

theorem moebiusLogSqSummatory_eq (x : ℝ) :
    moebiusLogSqSummatory x =
      arithmeticSummatory (arithmeticLogWeight (arithmeticLogWeight (μ : ArithmeticFunction ℝ))) x := by
  unfold moebiusLogSqSummatory arithmeticSummatory
  apply sum_congr rfl
  intro n _
  simp only [arithmeticLogWeight_apply, intCoe_apply]
  ring

theorem arithmeticSummatory_moebius_mul_centeredSelberg (c x : ℝ) (hx : 1 ≤ x) :
    arithmeticSummatory ((μ : ArithmeticFunction ℝ) * centeredSelbergCoefficient c) x =
      moebiusLogSqSummatory x - 2 * c := by
  rw [moebius_mul_centeredSelbergCoefficient, moebiusLogSqSummatory_eq]
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  simp [arithmeticSummatory, sub_eq_add_neg, ArithmeticFunction.one_apply,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, hfloor]

/-- The second hyperbola split, with real quotient arguments and exact overlap.-/
theorem moebiusSelberg_hyperbola (c x y z : ℝ)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hyz : y * z = x) :
    moebiusLogSqSummatory x - 2 * c =
      (∑ k ∈ Ioc 0 ⌊y⌋₊, centeredSelbergCoefficient c k * mertensReal (x / k)) +
      (∑ d ∈ Ioc 0 ⌊z⌋₊, (μ d : ℝ) * centeredSelbergSummatory c (x / d)) -
      centeredSelbergSummatory c y * mertensReal z := by
  rw [← arithmeticSummatory_moebius_mul_centeredSelberg c x hx, mul_comm]
  exact arithmeticSummatory_convolution_hyperbola (centeredSelbergCoefficient c)
    (μ : ArithmeticFunction ℝ) x y z hx hy hz hyz

theorem centeredSelbergSummatory_eq (c x : ℝ) :
    centeredSelbergSummatory c x =
      arithmeticSummatory (vonMangoldt * vonMangoldt) x - primeLogSummatory x -
        (2 * c) * (⌊x⌋₊ : ℝ) := by
  unfold centeredSelbergSummatory centeredSelbergCoefficient arithmeticSummatory primeLogSummatory
  have hterm : ∀ n ∈ Ioc 0 ⌊x⌋₊,
      ((vonMangoldt * vonMangoldt - arithmeticLogWeight vonMangoldt -
        (2 * c) • (ζ : ArithmeticFunction ℝ)) n) =
      (vonMangoldt * vonMangoldt) n - arithmeticLogWeight vonMangoldt n - 2 * c := by
    intro n hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Ioc.mp hn).1
    simp [sub_eq_add_neg, ArithmeticFunction.zeta_apply, hn0]
  simp_rw [sum_congr rfl hterm, sum_sub_distrib]
  simp [arithmeticSummatory, mul_comm]

/-- The symmetric prime convolution split at the exact real square root.-/
theorem vonMangoldt_convolution_sqrt (x : ℝ) (hx : 1 ≤ x) :
    arithmeticSummatory (vonMangoldt * vonMangoldt) x =
      2 * (∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, vonMangoldt n * Chebyshev.psi (x / n)) -
        (Chebyshev.psi (Real.sqrt x)) ^ 2 := by
  have hsqrt : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have h := arithmeticSummatory_convolution_hyperbola vonMangoldt vonMangoldt
    x (Real.sqrt x) (Real.sqrt x) hx hsqrt hsqrt (Real.mul_self_sqrt (by linarith))
  simpa only [arithmeticSummatory_vonMangoldt, ← two_mul, pow_two] using h

end TwinPrime.Analytic
