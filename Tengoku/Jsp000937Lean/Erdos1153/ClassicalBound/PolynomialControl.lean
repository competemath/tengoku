import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.RieszInterpolation
import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.ChebyshevDCT

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unconditional polynomial control

This file assembles the two independently verified polynomial estimates.  The
finite Riesz formula supplies the sharp weighted branch, while the explicit
Chebyshev expansion supplies the positive endpoint floor.  Together they
discharge the pointwise interface used by the clipped pair-energy argument.
-/

namespace Erdos1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- Every real polynomial satisfies the clipped Bernstein interface from its
own degree, interval, and supremum hypotheses.-/
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
polynomial.-/
theorem pointwiseClippedBernsteinAt_signedDerivativeRowPolynomial
    {n : ℕ} (nodes : OrderedNodes n) (j : Fin n) :
    PointwiseClippedBernsteinAt (n - 1)
      (signedDerivativeRowPolynomial nodes j) (nodes.point j)
      (lebesgueOn nodes.toNodeFamily (-1) 1) :=
  pointwiseClippedBernsteinAt _ _ _ _

end

end ClassicalBound
end Erdos1153
