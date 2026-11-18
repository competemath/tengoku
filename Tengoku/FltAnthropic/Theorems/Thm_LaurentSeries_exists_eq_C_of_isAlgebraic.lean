import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LaurentSeries_exists_eq_C_of_isAlgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LaurentSeries_exists_eq_C_of_isAlgebraic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u

/--
@isnad1 id=ex.1h2v.s8.cf1a6f4522ec from=translated src=- shape=82a056dc vocab=431d7573
-/
theorem LaurentSeries.exists_eq_C_of_isAlgebraic
    {K : Type u} [Field K] (x : LaurentSeries K) (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by exact @_root_.P2MW.S_LaurentSeries_exists_eq_C_of_isAlgebraic.solution K _ x hx
