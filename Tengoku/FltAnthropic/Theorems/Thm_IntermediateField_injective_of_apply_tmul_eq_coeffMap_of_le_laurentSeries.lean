import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem IntermediateField.injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries
    (κ : Type u) [Field κ] (k : Type v) [Field k] [Algebra κ k]
    (R : IntermediateField κ (LaurentSeries κ))
    (φ : k ⊗[κ] ↥R →ₐ[k] LaurentSeries k)
    (hφ : ∀ r : ↥R, φ (1 ⊗ₜ[κ] r) = ModularCurve.coeffMap (algebraMap κ k) ((r : ↥R) : LaurentSeries κ)) :
    Function.Injective φ := by exact @_root_.P2MW.S_IntermediateField_injective_of_apply_tmul_eq_coeffMap_of_le_laurentSeries.solution κ _ k _ _ R φ hφ
