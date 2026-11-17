import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve ModularCurve
/--
@isnad1 id=iff.0h3v.s9.361e1ea12d19 from=translated src=- shape=dba853dc vocab=767350e7
-/
theorem AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.deg = 1 ↔ Function.Surjective (algebraMap K v.ResidueField) := by exact @_root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField.solution K F _ _ _ v
