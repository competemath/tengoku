import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GenusNumerics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_twelve_mul_genusFormula.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_twelve_mul_genusFormula

open ModularCurve

/--
@isnad1 id=eq.0h1v.s6.ee60832b7a93 from=translated src=- shape=ee4844bc vocab=362af6e4
-/
theorem solution (N : ℕ) :
    12 * genusFormula N
      = 12 + (dedekindPsi N : ℚ) - 3 * (nuTwo N : ℚ) - 4 * (nuThree N : ℚ)
        - 6 * (cuspCount N : ℚ) := by
  unfold genusFormula
  ring
