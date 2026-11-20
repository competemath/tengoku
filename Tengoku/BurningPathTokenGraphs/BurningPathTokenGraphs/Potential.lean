import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The shelf potential

This file isolates the exact algebra of the shelf potential. Integer
feasibility and trajectory estimates build on these real identities.
-/

namespace BurningPath

/-- The shelf potential `Ψ(w,z) = 4w³/3 - z²`.-/
noncomputable def shelfPotential (w z : ℝ) : ℝ :=
  (4 / 3) * w ^ 3 - z ^ 2

/-- Exact expansion of the potential change under one formal shelf update.-/
theorem shelfPotential_update_identity (w z q : ℝ) :
    shelfPotential (w - q) (z - 2 * (w - q)) - shelfPotential w z =
      -4 * w ^ 2 * q + 4 * w * q ^ 2 - (4 / 3) * q ^ 3 +
        4 * (w - q) * z - 4 * (w - q) ^ 2 := by
  unfold shelfPotential
  ring

/-- The alternative expansion after writing `a = w-q`.-/
theorem shelfPotential_update_identity' (a z q : ℝ) :
    shelfPotential a (z - 2 * a) - shelfPotential (a + q) z =
      -4 * a ^ 2 * q - 4 * a * q ^ 2 - (4 / 3) * q ^ 3 +
        4 * a * z - 4 * a ^ 2 := by
  unfold shelfPotential
  ring

/-- The quadratic envelope used in equation (29).-/
theorem shelf_error_envelope {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    36 * (1 - x) + 8 * (1 - x) ^ 2 + 12 * x ≤ 44 := by
  nlinarith [sq_nonneg x, sq_nonneg (1 - x)]

theorem shelfPotential_le_cube (w z : ℝ) :
    shelfPotential w z ≤ (4 / 3) * w ^ 3 := by
  unfold shelfPotential
  nlinarith [sq_nonneg z]

/-- A positive lower bound on `Ψ` forces the corresponding lower bound on `w³`.-/
theorem cube_lower_of_shelfPotential_lower {w z E : ℝ}
    (hE : E ≤ shelfPotential w z) :
    (3 / 4) * E ≤ w ^ 3 := by
  have h := hE.trans (shelfPotential_le_cube w z)
  nlinarith

end BurningPath
