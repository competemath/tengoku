import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_GeometricBaseChange
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.isFractionRing_tensorProduct_laurentBaseChange
    (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    letI := ((ModularCurve.baseChangeHom L F₀).codRestrict (ModularCurve.laurentBaseChange L F₀).toSubalgebra
      (ModularCurve.baseChangeHom_mem L F₀)).toRingHom.toAlgebra
    IsFractionRing (L ⊗[ℚ] ↥F₀) ↥(ModularCurve.laurentBaseChange L F₀) := by exact @_root_.P2MW.S_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange.solution L _ _ F₀
