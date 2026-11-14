import Tengoku.Twinprime.TwinPrime.Analytic.Hyperbola

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complex arithmetic summation at real endpoints

The exact finite hyperbola identity is specialized to complex coefficients.
The quotient endpoints remain real and only the summation cutoffs are floored.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- Ordinary arithmetic summation at a real endpoint.-/
def complexArithmeticSummatory (f : ArithmeticFunction ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, f n

@[simp] theorem complexArithmeticSummatory_nat (f : ArithmeticFunction ℂ) (N : ℕ) :
    complexArithmeticSummatory f (N : ℝ) = ∑ n ∈ Ioc 0 N, f n := by
  simp [complexArithmeticSummatory]

/-- The real Dirichlet hyperbola identity, keeping each quotient real inside
the summatory function.-/
theorem complexArithmeticSummatory_convolution_hyperbola (f g : ArithmeticFunction ℂ)
    (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hyz : y * z = x) :
    complexArithmeticSummatory (f * g) x =
      (∑ k ∈ Ioc 0 ⌊y⌋₊, f k * complexArithmeticSummatory g (x / k)) +
      (∑ d ∈ Ioc 0 ⌊z⌋₊, g d * complexArithmeticSummatory f (x / d)) -
      complexArithmeticSummatory f y * complexArithmeticSummatory g z := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hlower : ⌊y⌋₊ * ⌊z⌋₊ ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    push_cast
    calc
      (⌊y⌋₊ : ℝ) * (⌊z⌋₊ : ℝ) ≤ y * z :=
        mul_le_mul (Nat.floor_le hy0.le) (Nat.floor_le hz0.le) (by positivity) hy0.le
      _ = x := hyz
  have hupper : ⌊x⌋₊ < (⌊y⌋₊ + 1) * (⌊z⌋₊ + 1) := by
    have hylt := Nat.lt_floor_add_one y
    have hzlt := Nat.lt_floor_add_one z
    have hreal : (⌊x⌋₊ : ℝ) < ((⌊y⌋₊ : ℝ) + 1) * ((⌊z⌋₊ : ℝ) + 1) := by
      calc
        _ ≤ x := Nat.floor_le hx0
        _ = y * z := hyz.symm
        _ < ((⌊y⌋₊ : ℝ) + 1) * z := mul_lt_mul_of_pos_right hylt hz0
        _ < _ := mul_lt_mul_of_pos_left hzlt (by positivity)
    exact_mod_cast hreal
  simpa only [complexArithmeticSummatory, Nat.floor_div_natCast] using
    sum_Ioc_convolution_hyperbola f g ⌊x⌋₊ ⌊y⌋₊ ⌊z⌋₊ hlower hupper

end TwinPrime.Analytic
