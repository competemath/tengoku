import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
    {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    [LocallyCompactSpace (GL (Fin 2) F)] [SecondCountableTopology (GL (Fin 2) F)]
    [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]
    (μ : Measure (GL (Fin 2) F)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by exact @_root_.P2MW.S_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two.solution F _ _ _ _ _ _ _ μ _
