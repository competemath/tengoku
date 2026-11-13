import Tengoku.LeanCommutator.PavingSeparation.PavingBasic
import Tengoku.LeanCommutator.PavingSeparation.Family
import Tengoku.LeanCommutator.PavingSeparation.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact optimal dyadic paving for the explicit family -/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

namespace PavingSeparation

/-- Coloring by the first l branches of the original recursive coordinate tree.-/
def dyadicColor : (m l : ℕ) → l ≤ m → Cube m → Cube l
  | _, 0, _ => fun _ ↦ 0
  | 0, l + 1, h => False.elim (by omega)
  | m + 1, l + 1, h =>
      Sum.map (dyadicColor m l (Nat.le_of_succ_le_succ h))
        (dyadicColor m l (Nat.le_of_succ_le_succ h))

end PavingSeparation
