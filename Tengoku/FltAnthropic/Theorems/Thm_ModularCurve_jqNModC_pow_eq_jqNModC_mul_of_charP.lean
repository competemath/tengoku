import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.jqNModC_pow_eq_jqNModC_mul_of_charP
    (K : Type) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] (n : ℕ) [NeZero n] [NeZero (q * n)] :
    (jqNModC K n) ^ q = jqNModC K (q * n) := by exact @_root_.P2MW.S_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP.solution K _ q _ _ n _ _
