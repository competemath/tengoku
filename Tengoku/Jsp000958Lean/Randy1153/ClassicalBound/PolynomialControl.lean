import Tengoku.Jsp000958Lean.Randy1153.ClassicalBound.RieszInterpolation
import Tengoku.Jsp000958Lean.Randy1153.ClassicalBound.ChebyshevDCT

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unconditional polynomial control

This file assembles the two independently verified polynomial estimates.  The
finite Riesz formula supplies the sharp weighted branch, while the explicit
Chebyshev expansion supplies the positive endpoint floor.  Together they
discharge the pointwise interface used by the clipped pair-energy argument.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- Every real polynomial satisfies the clipped Bernstein interface from its
own degree, interval, and supremum hypotheses.
@isnad1 id=pointwis.0h4v.s3.549ae0c9b853 from=translated src=- shape=5f7b4f7c vocab=8957bfba
-/
theorem pointwiseClippedBernsteinAt (d : ℕ) (p : ℝ[X]) (x M : ℝ) :
    PointwiseClippedBernsteinAt d p x M := by
  cases d with
  | zero =>
      intro hd
      omega
  | succ d =>
      intro hd hpdeg hx hsup
      have hM : 0 ≤ M :=
        (abs_nonneg (p.eval x)).trans (hsup x hx)
      have hexp : BoundedChebyshevExpansion (d + 1) p M :=
        boundedChebyshevExpansion_of_natDegree_le_of_sup_le hM hpdeg hsup
      have hweighted : RootWeightedBernsteinAt (d + 1) p x M :=
        weighted_bernstein_of_pos (d + 1) (by omega) p hpdeg M hsup hx
      exact
        (pointwiseClippedBernsteinAt_of_boundedExpansion_of_rootWeighted
          hM hexp hweighted) hd hpdeg hx hsup

/-- Unconditional clipped Bernstein control for every signed derivative-row
polynomial.
@isnad1 id=pointwis.0h3v.s5.4fc6e8dc4581 from=translated src=- shape=9d62c522 vocab=446d0d20
-/
theorem pointwiseClippedBernsteinAt_signedDerivativeRowPolynomial
    {n : ℕ} (nodes : OrderedNodes n) (j : Fin n) :
    PointwiseClippedBernsteinAt (n - 1)
      (signedDerivativeRowPolynomial nodes j) (nodes.point j)
      (lebesgueOn nodes.toNodeFamily (-1) 1) :=
  pointwiseClippedBernsteinAt _ _ _ _

end

end ClassicalBound
end Randy1153
