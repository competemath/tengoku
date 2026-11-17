import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ValuationSubring.exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic
    {E F : Type*} [Field E] [Field F] [Algebra E F] [Algebra.IsAlgebraic E F]
    (O : ValuationSubring F) {g : F} (hg : g ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : E, c ≠ 0 ∧ O.valuation (g ^ n) = O.valuation (algebraMap E F c) := by exact @_root_.P2MW.S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic.solution E F _ _ _ _ O g hg
