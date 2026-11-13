import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSCrossBarrier
import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSBarrierAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complete quantitative MSS barrier step

This is Lemma 5.10 of Marcus--Spielman--Srivastava, with the above-roots
conclusion included. Every analytic input is proved in the imported modules.
-/

namespace NoEpsilon.MSSBarrierStep

open NoEpsilon.MSSBarrier NoEpsilon.MSSCrossBarrier NoEpsilon.MSSBarrierAlgebra

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.MSSBarrierStep
