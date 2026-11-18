import Tengoku.Barbier.Barbier.Reuleaux
import Tengoku.Barbier.Barbier.ArclenFinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace Barbier

open Real MeasureTheory intervalIntegral Set eVariationOn ENNReal Complex

/-! ### Helper: HasDerivAt for cos(θ - c) -/

/-! ### Continuity of curve (reuleaux w) -/

/-! ### Corner pieces: curve is constant -/

/-! ### eVariationOn on corner pieces is zero -/

/-! ### Arc pieces -/

/-! ### eVariation on corner subsets -/

/-! ### Partition points for main theorem -/

private noncomputable def segPts : ℕ → ℝ
  | 0 => 0
  | 1 => π / 6
  | 2 => π / 2
  | 3 => 5 * π / 6
  | 4 => 7 * π / 6
  | 5 => 3 * π / 2
  | 6 => 11 * π / 6
  | _ => 2 * π

/-! ### Main theorem -/

end Barbier
end
