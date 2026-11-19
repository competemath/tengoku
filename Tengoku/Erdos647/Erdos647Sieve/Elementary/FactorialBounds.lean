/-
Factorial estimates obtained from Mathlib's Stirling development.
No proof of Stirling's formula is copied or reconstructed here.
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Stirling
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped Topology
open Filter Real

noncomputable section
namespace Erdos647Sieve.Elementary

/-- The exact correction term in the library's logarithmic Stirling formula.
@isnad1 id=eq.1h1v.s6.89fbc0b6399e from=translated src=- shape=d705ab0d vocab=ca5f636e
-/
theorem log_factorial_decomposition (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Nat.factorial n : ℝ) =
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (n : ℝ) / 2 +
        (Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0,
      Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- A global upper bound: in particular, the linear term is not lost.
@isnad1 id=le.1h1v.s6.8f659ec8b5a2 from=translated src=- shape=81fbf457 vocab=009f3b13
-/
theorem log_factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (Nat.factorial n : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (n : ℝ) / 2 + 1 := by
  rcases n with _ | m
  · omega
  have hd := log_factorial_decomposition (m + 1) (by omega)
  have hfirst : Real.log (Stirling.stirlingSeq 1) + Real.log 2 / 2 = 1 := by
    have h := log_factorial_decomposition 1 (by norm_num)
    norm_num only [Nat.factorial_one, Nat.cast_one, Real.log_one, mul_zero,
      zero_sub, zero_div, add_zero] at h
    linarith
  have hs : Real.log (Stirling.stirlingSeq (m + 1)) ≤
      Real.log (Stirling.stirlingSeq 1) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one, zero_add] using
      (Stirling.log_stirlingSeq'_antitone (Nat.zero_le m))
  linarith

/-- A lower bound sufficient for the varying-numerator factorial tail.
@isnad1 id=le.1h1v.s5.c3d72d0bd444 from=translated src=- shape=34e689d6 vocab=25518754
-/
theorem log_factorial_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) ≤
      Real.log (Nat.factorial n : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

/-- Unlike a fixed-numerator series limit, this lower bound is usable uniformly.
@isnad1 id=le.0h1v.s5.1985d72498c0 from=translated src=- shape=0f1664f2 vocab=38f987ca
-/
theorem factorial_pow_lower (n : ℕ) :
    ((n : ℝ) / Real.exp 1) ^ n ≤ (Nat.factorial n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h := Real.exp_le_exp.mpr (log_factorial_lower n hn)
  have he : Real.exp ((n : ℝ) * Real.log (n : ℝ) - (n : ℝ)) =
      ((n : ℝ) / Real.exp 1) ^ n := by
    calc
      _ = Real.exp (Real.log (((n : ℝ) / Real.exp 1) ^ n)) := by
        congr 1
        rw [Real.log_pow, Real.log_div hnR.ne' (Real.exp_ne_zero 1),
            Real.log_exp]
        ring
      _ = _ := Real.exp_log (pow_pos (div_pos hnR (Real.exp_pos 1)) n)
  rw [he, Real.exp_log (by positivity : 0 < (Nat.factorial n : ℝ))] at h
  exact h

end Erdos647Sieve.Elementary
end
