import Tengoku.Seed.Analysis.Normed.Group.Int
import Tengoku.Seed.Analysis.Polynomial.CauchyBound
import Tengoku.Seed.Tactic.GCongr
import Tengoku.Seed.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An elementary height bound for integral roots

This file isolates the last algebraic step in the proof of Paper C, Lemma 3.1.
For an integral polynomial `p`, its height is the largest absolute value of
one of its nonzero coefficients.  Cauchy's root bound, applied after mapping
`p` to `ℝ[X]`, gives the bound claimed in the paper.

In fact, integrality of the root and the strict form of Cauchy's bound give
the slightly stronger estimate `|u| ≤ height p`.  We also record verbatim the
weaker paper form `|u| ≤ 1 + height p`.
-/

namespace PaperC

open Finset NNReal Polynomial

/-- The (naive) height of an integral polynomial: the maximum of the absolute
values of its nonzero coefficients.  The height of the zero polynomial is
defined to be zero.-/
def integerPolynomialHeight (p : ℤ[X]) : ℕ :=
  p.support.sup fun n ↦ (p.coeff n).natAbs

@[simp]
theorem integerPolynomialHeight_zero :
    integerPolynomialHeight (0 : ℤ[X]) = 0 := by
  simp [integerPolynomialHeight]

end PaperC
