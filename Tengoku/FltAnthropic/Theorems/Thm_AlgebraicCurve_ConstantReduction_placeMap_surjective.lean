import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_ConstantReduction
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_ConstantReduction_placeMap_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_ConstantReduction_placeMap_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve

theorem AlgebraicCurve.ConstantReduction.placeMap_surjective
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) [HasPrincipalDivisors L F] :
    Function.Surjective R.placeMap := by exact @_root_.P2MW.S_AlgebraicCurve_ConstantReduction_placeMap_surjective.solution L _ A F _ _ Fbar _ _ R _
