import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_IsCurveOver
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_existsUnique_pDigits_of_D_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_existsUnique_pDigits_of_D_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem AlgebraicCurve.existsUnique_pDigits_of_D_ne_zero {K : Type*} {F : Type*} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : KaehlerDifferential.D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by exact @_root_.P2MW.S_AlgebraicCurve_existsUnique_pDigits_of_D_ne_zero.solution K F _ _ _ _ p _ _ _ x _ t hdt g
