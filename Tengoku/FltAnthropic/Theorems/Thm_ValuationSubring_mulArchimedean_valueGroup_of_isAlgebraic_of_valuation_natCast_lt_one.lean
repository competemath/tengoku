import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=mularchi.2h3v.s8.2a5b0e052236 from=translated src=- shape=04ff4518 vocab=f94c7f57
-/
theorem ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1) :
    MulArchimedean A.ValueGroup := by exact @_root_.P2MW.S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one.solution K _ _ _ A p hp hAp
