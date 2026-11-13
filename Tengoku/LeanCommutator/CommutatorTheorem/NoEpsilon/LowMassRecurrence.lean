import Tengoku.Seed.Data.Real.Sqrt
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The balanced paving recurrence

This file solves the actual square-root recurrence produced by paired MSS
selection. Its constants are independent of the number of groups.
-/

namespace NoEpsilon.LowMassPaving

noncomputable def transversalConstant (D : ℝ) : ℝ :=
  (1 + 2 * (Real.sqrt 2 + 1) * Real.sqrt D) ^ 2

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.LowMassPaving
