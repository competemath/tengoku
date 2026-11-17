import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.charZero_functionField_of_hom_spec_of_charZero
    (X : Scheme.{0}) [IsIntegral X]
    (C : Type) [Field C] [CharZero C] (f : Spec (CommRingCat.of C) ⟶ X) :
    CharZero X.functionField := by exact @_root_.P2MW.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero.solution X _ C _ _ f
