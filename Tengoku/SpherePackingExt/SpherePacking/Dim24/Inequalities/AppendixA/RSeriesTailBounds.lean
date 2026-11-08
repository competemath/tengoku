module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.Constants
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.CoeffBoundConstants
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Tail bounds for `r`-series (`r = exp(-π t)`) used in Appendix A.

This file packages the geometric tail estimates that correspond to the PARI/GP
`PolynomialSum(..., 1/23, 100, ...)` checks in `appendix.txt`.
-/

open scoped BigOperators Real

namespace SpherePacking.Dim24.AppendixA

noncomputable section

lemma const_psi_tail_lt_eps :
    ((2 : ℚ) * ((44 : ℚ) * (16 : ℚ) * (24 : ℚ) ^ (7 : ℕ)) * (101 : ℚ) ^ (20 : ℕ) *
        ((1 : ℚ) / 23) ^ (88 : ℕ)) <
      (10 : ℚ) ^ (-50 : ℤ) := by
  -- A closed rational inequality; `norm_num` clears denominators.
  set_option maxRecDepth 6000 in
  norm_num

end

end SpherePacking.Dim24.AppendixA
