/-
Combine the two finite-list estimates with the accepted even Bonferroni bound.
NEW IMPLEMENTATION: not compiled in the assistant environment.
-/
import Tengoku.Erdos647.Erdos647Sieve.CoefficientBounds
import Tengoku.Erdos647.Erdos647Sieve.ExponentialProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Erdos647Sieve.Bonferroni

/-- The analytic majorant for an arbitrary even weighted truncation.
This is a finite-list result, not a claim about independent arithmetic events.-/
theorem even_truncation_le_exp_add_tail (xs : List ℝ)
    (h : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) (J : ℕ) (hJ : Even J) :
    truncation xs J ≤ Real.exp (-xs.sum) +
      xs.sum ^ (J + 1) / (Nat.factorial (J + 1) : ℝ) := by
  exact (even_bounds xs h J hJ).2.trans
    (add_le_add (avoidProduct_le_exp_neg_sum xs h)
      (elementary_le_pow_sum_div_factorial xs (fun a ha => (h a ha).1) (J + 1)))

/-- The same majorant for the actual alternating sum.-/
theorem even_sum_le_exp_add_tail (xs : List ℝ)
    (h : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) (J : ℕ) (hJ : Even J) :
    (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j * elementary xs j) ≤
      Real.exp (-xs.sum) + xs.sum ^ (J + 1) / (Nat.factorial (J + 1) : ℝ) := by
  simpa only [← truncation_eq_sum] using even_truncation_le_exp_add_tail xs h J hJ

end Erdos647Sieve.Bonferroni
end
