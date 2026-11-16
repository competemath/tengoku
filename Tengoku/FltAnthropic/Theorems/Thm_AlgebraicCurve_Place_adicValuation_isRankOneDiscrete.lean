import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
/--
@isnad1 id=isrankon.0h3v.s5.a529a5c0f8c9 from=translated src=- shape=4a2062f4 vocab=77da76b6
-/
theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete := by exact @_root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.solution K F _ _ _ v
