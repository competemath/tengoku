import Tengoku.Leancert.LeanCert.Analysis.SeriesTail
import Tengoku.Seed.Analysis.SpecialFunctions.Exp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Discrete Gaussian majorants. These bound series, not improper integrals
or a heat-flow representation. -/
namespace LeanCert.Analysis.SeriesTail

/-- The discrete quadratic exponent has a geometric majorant beyond any
natural cutoff, with ratio strictly below one when `a > 0`.
@isnad1 id=le.1h3v.s7.90200f89664c from=translated src=- shape=f608d7ea vocab=fc51e49d
-/
theorem gaussian_le_geometric (a : ℝ) (ha : 0 ≤ a) (N k : ℕ) :
    Real.exp (-a * ((k+N : ℕ) : ℝ)^2) ≤
      Real.exp (-a * (N : ℝ)^2) * (Real.exp (-a * (2*(N : ℝ)+1)))^k := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hk : (k : ℝ) ≤ (k : ℝ)^2 := by exact_mod_cast (show k ≤ k^2 by nlinarith)
  push_cast
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hk)]

/-- Gaussian norm domination proves convergence and an explicit truncation
error in any complete normed additive group (in particular ℝ or ℂ).
@isnad1 id=and.3h5v.s8.8b0f52af90b2 from=translated src=- shape=90f4cfa9 vocab=ba89a0b9
-/
theorem of_gaussian {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (N : ℕ) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hbound : ∀ k, ‖f (k+N)‖ ≤ C * Real.exp (-a * ((k+N : ℕ) : ℝ)^2)) :
    Summable f ∧ ‖(∑' n, f n) - ∑ n ∈ Finset.range N, f n‖ ≤
      C * Real.exp (-a * (N : ℝ)^2) / (1 - Real.exp (-a * (2*(N : ℝ)+1))) := by
  apply of_geometric
  · exact (Real.exp_pos _).le
  · rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos ha) (by positivity)
  · intro k
    exact (hbound k).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (gaussian_le_geometric a ha.le N k) hC)

end LeanCert.Analysis.SeriesTail
