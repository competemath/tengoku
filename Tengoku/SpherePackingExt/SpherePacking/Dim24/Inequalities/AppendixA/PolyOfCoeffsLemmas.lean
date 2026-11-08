/-
Lemmas about `AppendixA.polyOfCoeffs` needed for Appendix A inequality arguments.

These are lightweight, self-contained facts used to turn coefficient lists into explicit
finite sums, and to extract coefficients.
-/
module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.Polynomials.Basic
public import Tengoku.Seed.Algebra.Algebra.Basic
public import Tengoku.Seed.Algebra.Algebra.Rat
public import Tengoku.Seed.Algebra.Polynomial.Coeff
public import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.Algebra.BigOperators.Ring.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
`absBound` and the basic tail estimate for `polyOfCoeffs`.

We use the recursion `polyOfCoeffs (a :: l) = C a + X * polyOfCoeffs l`, so evaluation satisfies
`eval (a :: l) = a + x * eval l`. This makes it easy to bound `|eval|` on `|x| ≤ c`.
-/

open scoped BigOperators

namespace SpherePacking.Dim24.AppendixA

noncomputable section

/--
`absBound l c` is the explicit bound `∑ |aᵢ| * c^i` corresponding to a coefficient list `l`.

It is used to bound `|(polyOfCoeffs l).eval₂ _ x|` on `|x| ≤ c`.-/
@[expose]
public def absBound : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: l, c => |(algebraMap ℚ ℝ) a| + c * absBound l c

@[simp] public lemma absBound_nil (c : ℝ) : absBound [] c = 0 := rfl

@[simp] public lemma absBound_cons (a : ℚ) (l : List ℚ) (c : ℝ) :
    absBound (a :: l) c = |(algebraMap ℚ ℝ) a| + c * absBound l c := rfl

/-!
### Sign lemmas for coefficient lists

These are used to replace the PARI/GP "Sturm check" steps in Appendix A by simple
monotonicity/sign arguments when all coefficients have the same sign.
-/

end

end SpherePacking.Dim24.AppendixA
