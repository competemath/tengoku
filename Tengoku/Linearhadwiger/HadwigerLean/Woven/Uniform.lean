import Tengoku.Linearhadwiger.HadwigerLean.Woven.UniformClique
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A complete-minor quantitative woven bound for all finite pair budgets. -/

namespace HadwigerLean.Woven

/-- A natural upper bound on the KT density needed for a complete minor
on every normalized role slot.-/
noncomputable def uniformCliqueQ (a b : ℕ) : ℕ :=
  (a + 2 * b) +
    ⌈30 * ((2 * (a + 2 * b) : ℕ) : ℝ) *
      Real.sqrt (Real.log ((2 * (a + 2 * b) : ℕ) : ℝ))⌉₊

/-- Connectivity sufficient for the complete-minor proof of wovenness.-/
noncomputable def uniformCliqueK (a b : ℕ) : ℕ :=
  (a + 2 * b) + 2 * uniformCliqueQ a b

end HadwigerLean.Woven
