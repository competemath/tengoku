import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RatFuncPlaces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `#p2m_type_eq_warn`, 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
/--
@isnad1 id=isequiv.1h5v.s6.4490bca6025c from=translated src=- shape=42bf9343 vocab=1535943b
-/
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation := by exact @_root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.solution K F _ _ _ v Γ _ w h

