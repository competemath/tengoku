/-
Geometric-series tail bounds used in Appendix A truncation arguments.

This file provides a lightweight alternative to the `MonomialSum`/`PolynomialSum` computations in
`appendix.txt`: instead of a closed form for `∑ n^k q^n`, we bound the tail by proving that the
terms form a geometric progression up to a uniform ratio.
-/
module
public import Tengoku.Seed.Analysis.SpecificLimits.Basic
public import Tengoku.Seed.Topology.Instances.ENNReal.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Geometric-series tail bounds for terms of the form `(n + 1)^k * q^n`.

The key step is a uniform bound on successive ratios of `powGeomTerm`, expressed by
`powGeomRatio`. This yields computable tail estimates for series of the form
`∑' m, powGeomTerm q k (N + m)`, including the convenient specialization
`tsum_powGeomTerm_tail_le_two_mul` when the ratio is at most `1/2`.
-/

open scoped BigOperators Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/-- The basic term `(n+1)^k * q^n` that appears when bounding coefficients by polynomials in `n`.-/
@[expose]
public def powGeomTerm (q : ℝ) (k : ℕ) (n : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ k) * q ^ n

/-- A uniform bound on successive ratios of `powGeomTerm` starting at `N`.-/
@[expose]
public def powGeomRatio (q : ℝ) (k N : ℕ) : ℝ :=
  q * (((N + 2 : ℝ) / (N + 1 : ℝ)) ^ k)

lemma add_two_div_add_one_eq_one_add_one_div (n : ℕ) :
    ((n + 2 : ℝ) / (n + 1 : ℝ)) = 1 + (1 / (n + 1 : ℝ)) := by
  field_simp [(by positivity : (n + 1 : ℝ) ≠ 0)]
  ring

lemma add_two_div_add_one_le_of_le {N n : ℕ} (hn : N ≤ n) :
    ((n + 2 : ℝ) / (n + 1 : ℝ)) ≤ ((N + 2 : ℝ) / (N + 1 : ℝ)) := by
  have hdiv : (1 / (n + 1 : ℝ)) ≤ (1 / (N + 1 : ℝ)) := by
    refine one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N + 1 : ℝ)) ?_
    exact_mod_cast Nat.succ_le_succ hn
  simpa [add_two_div_add_one_eq_one_add_one_div] using add_le_add_left hdiv 1

end

end SpherePacking.Dim24.AppendixA
