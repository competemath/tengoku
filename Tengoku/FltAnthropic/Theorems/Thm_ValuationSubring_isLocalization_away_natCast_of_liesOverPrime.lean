import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open AlgebraicGeometry

/--
@isnad1 id=away.2h2v.s8.d5b952cc0f0c from=translated src=- shape=6f3b2a7c vocab=4dc7038f
-/
theorem ValuationSubring.isLocalization_away_natCast_of_liesOverPrime
    (O : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) (hp : p.Prime) (hO : O.LiesOverPrime p) :
    IsLocalization.Away ((p : ℕ) : ↥O) (AlgebraicClosure ℚ) := by exact @_root_.P2MW.S_ValuationSubring_isLocalization_away_natCast_of_liesOverPrime.solution O p hp hO
