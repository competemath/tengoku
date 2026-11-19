import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelPieces
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelDisjointness
import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.RawModelStage
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonzero CI stage model from old and child models

The terminal owner map chooses one branch for every path. The old
model and the p rooted child models provide all clique edges.
The remaining assumptions express the cleaned geometric placement of
the paths and connected D patches; this theorem verifies the assembled
model, its exact H3 tangency, and its new core.
-/

namespace HadwigerLean.Inseparability

universe u

abbrev CIRawIndex (p x : ℕ) :=
  Sum (Fin p × Fin x) (Fin x)

abbrev CIPathIndex (p x : ℕ) :=
  Fin ((4 * p + 1) * x)

end HadwigerLean.Inseparability
