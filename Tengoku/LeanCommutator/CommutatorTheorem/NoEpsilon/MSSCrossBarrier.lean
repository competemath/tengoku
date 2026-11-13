import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSSpecialization
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSResidues
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSReducedFraction
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSPartialFractions
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSResidueBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cross-coordinate MSS barrier as a finite positive-residue sum

Real stability supplies every hypothesis of the partial-fraction expansion:
real poles, simple reduced denominator, positive residues, and bounded degree.
-/

namespace NoEpsilon.MSSCrossBarrier

open Polynomial NoEpsilon.MSSStability NoEpsilon.MSSBarrier
open NoEpsilon.MSSSpecialization NoEpsilon.MSSResidues NoEpsilon.MSSReducedFraction
open NoEpsilon.MSSPartialFractions NoEpsilon.MSSResidueBounds
open scoped BigOperators Topology

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.MSSCrossBarrier
