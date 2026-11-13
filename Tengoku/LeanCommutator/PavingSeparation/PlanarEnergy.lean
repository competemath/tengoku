import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Algebra.Order.Floor.Ring
import Tengoku.Seed.Algebra.Order.BigOperators.Ring.Finset
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inverse-square energy in a bounded planar square

A clipped grid has exactly four to the scale many cells, including the boundary.
Retaining the exact collision count gives an explicit lower bound for the energy.
No optimality is claimed for its coefficient: for four points, this bound is `36 / 32`,
whereas the diameter of the square already gives `12 / 8`.
-/

namespace PavingSeparation.PlanarEnergy

open scoped BigOperators

private noncomputable def coordColor (q : ℕ) (hq : 0 < q) (x : ℝ) : Fin q :=
  ⟨min ⌊(x + 1) * q / 2⌋₊ (q - 1),
    lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

private noncomputable def pointColor {ι : Type*} (z : ι → ℂ)
    (_hz : ∀ i, |(z i).re| ≤ 1 ∧ |(z i).im| ≤ 1) (k : ℕ) (i : ι) :
    Fin (2 ^ k) × Fin (2 ^ k) :=
  (coordColor (2 ^ k) (by positivity) (z i).re, coordColor (2 ^ k) (by positivity) (z i).im)

end PavingSeparation.PlanarEnergy
