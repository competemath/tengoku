import Tengoku.Twinprime.TwinPrime.Analytic.ComplexHyperbola
import Tengoku.Seed.Analysis.Real.Sqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cancellation for a convolution of two bounded sequences

The exact square-root hyperbola split uses cancellation in each factor.
The overlap uses one cancellation bound and one length bound, preserving
a single power of the partial-sum constant.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/--
@isnad1 id=le.2h2v.s5.925f4bda5daf from=translated src=- shape=48404316 vocab=0a8d040c
-/
theorem norm_complexArithmeticSummatory_le_length (f : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    ‖complexArithmeticSummatory f x‖ ≤ x := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1 : ℝ) := sum_le_sum fun n _ => hf n
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

/-- A hyperbola strip costs its length times the inner cancellation budget.
@isnad1 id=le.4h5v.s7.77ca697b6c20 from=translated src=- shape=395634a4 vocab=2048efa5
-/
theorem norm_complex_hyperbola_strip_le (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ N : ℕ, ‖∑ n ∈ Ioc 0 N, g n‖ ≤ C)
    (x y : ℝ) (hy : 0 ≤ y) :
    ‖∑ k ∈ Ioc 0 ⌊y⌋₊, f k * complexArithmeticSummatory g (x / k)‖ ≤ y * C := by
  calc
    _ ≤ ∑ k ∈ Ioc 0 ⌊y⌋₊, ‖f k * complexArithmeticSummatory g (x / k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Ioc 0 ⌊y⌋₊, C := by
      apply sum_le_sum
      intro k _
      rw [norm_mul]
      exact (mul_le_mul (hf k) (hG _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul C)
    _ = (⌊y⌋₊ : ℝ) * C := by simp
    _ ≤ y * C := mul_le_mul_of_nonneg_right (Nat.floor_le hy) hC

/-- Two uniformly bounded partial sums give square-root cancellation for
their actual Dirichlet convolution.
@isnad1 id=le.6h4v.s7.5408978f3530 from=translated src=- shape=0611c438 vocab=5e37bf9c
-/
theorem norm_convolution_summatory_le_three_mul_sqrt (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ N : ℕ, ‖∑ n ∈ Ioc 0 N, f n‖ ≤ C)
    (hG : ∀ N : ℕ, ‖∑ n ∈ Ioc 0 N, g n‖ ≤ C)
    (x : ℝ) (hx : 1 ≤ x) :
    ‖complexArithmeticSummatory (f * g) x‖ ≤ 3 * C * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hsqrt0 := Real.sqrt_nonneg x
  have hsqrt1 : 1 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by simpa using hx)
  rw [complexArithmeticSummatory_convolution_hyperbola f g x (Real.sqrt x) (Real.sqrt x)
    hx hsqrt1 hsqrt1 (Real.mul_self_sqrt hx0)]
  have hA := norm_complex_hyperbola_strip_le f g hf C hC hG x (Real.sqrt x) hsqrt0
  have hB := norm_complex_hyperbola_strip_le g f hg C hC hF x (Real.sqrt x) hsqrt0
  have hO : ‖complexArithmeticSummatory f (Real.sqrt x) *
      complexArithmeticSummatory g (Real.sqrt x)‖ ≤ C * Real.sqrt x := by
    rw [norm_mul]
    exact mul_le_mul (hF _) (norm_complexArithmeticSummatory_le_length g hg _ hsqrt0)
      (norm_nonneg _) hC
  have htriangle := (norm_sub_le
    ((∑ k ∈ Ioc 0 ⌊Real.sqrt x⌋₊, f k * complexArithmeticSummatory g (x / k)) +
      ∑ k ∈ Ioc 0 ⌊Real.sqrt x⌋₊, g k * complexArithmeticSummatory f (x / k))
    (complexArithmeticSummatory f (Real.sqrt x) * complexArithmeticSummatory g (Real.sqrt x))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  nlinarith

end TwinPrime.Analytic
