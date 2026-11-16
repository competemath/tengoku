import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RatFuncPlaces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `#p2m_type_eq_warn`, 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
/--
@isnad1 id=iff.0h4v.s9.a3875507a860 from=translated src=- shape=d05d694b vocab=214d4958
-/
theorem P2M.Dup.AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by exact @_root_.P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.solution K F _ _ _ v a

