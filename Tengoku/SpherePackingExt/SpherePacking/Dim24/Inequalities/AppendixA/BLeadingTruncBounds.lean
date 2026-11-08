module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.PolyOfCoeffsLemmas
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.NormNum.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Lower bound for `AppendixA.Bleading_trunc` on `0 ≤ x ≤ 1/23`.

The original PARI/GP verification (Appendix A, Lemma `Bleadingterms`) uses Sturm's theorem.
In this repo we avoid implementing a full Sturm procedure by giving a direct coefficient-based
lower bound: we factor off the initial `X^4`, then bound the remaining polynomial from below by
keeping the constant term and (at `x = 1/23`) all *negative* coefficients, discarding the
nonnegative ones.
-/

namespace SpherePacking.Dim24.AppendixA

noncomputable section

open scoped BigOperators

private def cQ : ℚ := (1 : ℚ) / 23

private def negPart (a : ℚ) : ℚ := if a < 0 then a else 0

private def Bleading_trunc_tail : List ℚ := Bleading_trunc_coeffs.drop 4

/-- A uniform lower bound for `polyOfCoeffs (Bleading_trunc_coeffs.drop 4)` on `0 ≤ x ≤ 1/23`.-/
public def Bleading_trunc_c0Q : ℚ :=
  ∑ n ∈ Finset.range Bleading_trunc_tail.length,
    if n = 0 then Bleading_trunc_tail.getD 0 0 else negPart (Bleading_trunc_tail.getD n 0) * cQ ^ n

lemma one_div_25_lt_Bleading_trunc_c0Q : (1 : ℚ) / 25 < Bleading_trunc_c0Q := by
  simp [Bleading_trunc_c0Q, Bleading_trunc_tail, Bleading_trunc_coeffs, negPart, cQ,
    Finset.sum_range_succ]
  norm_num

lemma Bleading_trunc_c0Q_pos : 0 < Bleading_trunc_c0Q :=
  (show (0 : ℚ) < (1 : ℚ) / 25 by norm_num).trans one_div_25_lt_Bleading_trunc_c0Q

lemma Bleading_trunc_c0_pos : (0 : ℝ) < (Bleading_trunc_c0Q : ℝ) := by
  exact_mod_cast Bleading_trunc_c0Q_pos

end

end SpherePacking.Dim24.AppendixA
