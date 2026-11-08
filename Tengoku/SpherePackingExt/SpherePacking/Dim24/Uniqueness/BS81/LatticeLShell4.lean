module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LatticeL

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Elementary facts about `latticeShell4`

This file records elementary facts about `twoCodeVectors C` and the norm-`4` shell
`latticeShell4 C`. These are the easy direction of BS81 Lemma 17:
`twoCodeVectors C ⊆ latticeShell4 C`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

end
end SpherePacking.Dim24.Uniqueness.BS81
