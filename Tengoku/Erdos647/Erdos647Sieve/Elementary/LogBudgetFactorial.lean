/-
An exact finite-sum bridge between the protected integer logBudget and the
shifted real logarithm of a factorial. No asymptotic hypothesis is used.
-/
import Tengoku.Erdos647.Erdos647Sieve.Specification
import Tengoku.Erdos647.Erdos647Sieve.Elementary.FactorialEstimate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators
open Finset Real

noncomputable section
namespace Erdos647Sieve.Elementary

/-- The one-step recurrence for the exact shifted factorial expression.
@isnad1 id=eq.0h1v.s5.c3d167e3b3e0 from=translated src=- shape=c2d66bb6 vocab=5d2f71ce
-/
theorem shiftedFactorialLog_succ (H : ℕ) :
    shiftedFactorialLog (H + 1) =
      shiftedFactorialLog H + Real.log ((H : ℝ) + 3) := by
  have he : (Nat.factorial (H + 1 + 2) : ℝ) / 2 =
      ((H : ℝ) + 3) * ((Nat.factorial (H + 2) : ℝ) / 2) := by
    rw [show H + 1 + 2 = (H + 2) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  unfold shiftedFactorialLog
  rw [he, Real.log_mul (by positivity) (by positivity)]
  ring

/-- Sum of shifted logarithms, including the empty sum at H=0.
@isnad1 id=eq.0h1v.s5.60eaa3a7c8f5 from=translated src=- shape=574ef0ff vocab=f3196320
-/
theorem sum_log_shift_eq_factorial (H : ℕ) :
    (∑ k ∈ Finset.Icc 1 H, Real.log ((k : ℝ) + 2)) = shiftedFactorialLog H := by
  induction H with
  | zero => norm_num [shiftedFactorialLog]
  | succ H ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, shiftedFactorialLog_succ]
    congr 2
    push_cast
    ring

/-- The precise integer-floor budget is bounded by the real factorial expression.
@isnad1 id=le.0h1v.s4.d7be3e3aa12d from=translated src=- shape=d28016fd vocab=9d284a4a
-/
theorem logBudget_le_factorial (H : ℕ) :
    (Erdos647Sieve.logBudget H : ℝ) ≤ shiftedFactorialLog H / Real.log 2 := by
  unfold Erdos647Sieve.logBudget
  push_cast
  calc
    (∑ k ∈ Finset.Icc 1 H,
        (Int.floor (Real.log ((k : ℝ) + 2) / Real.log 2) : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 H, Real.log ((k : ℝ) + 2) / Real.log 2 := by
      exact Finset.sum_le_sum (fun k hk => Int.floor_le _)
    _ = (∑ k ∈ Finset.Icc 1 H, Real.log ((k : ℝ) + 2)) / Real.log 2 :=
      by simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = shiftedFactorialLog H / Real.log 2 := by rw [sum_log_shift_eq_factorial]

end Erdos647Sieve.Elementary
end
