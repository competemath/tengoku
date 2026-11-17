import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RatFuncPlaces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `#p2m_type_eq_warn`, 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
/--
@isnad1 id=iff.0h4v.s7.833806a2b7e6 from=translated src=- shape=c3d0343d vocab=48e929d1
-/
theorem P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by exact @_root_.P2MW.S_AlgebraicCurve_Place_mem_iff_adicValuation_le_one.solution K F _ _ _ v f

