import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_IsCurveOver
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Differentials
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_pDigits_existsUnique

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_pDigits_existsUnique.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open KaehlerDifferential

/--
@isnad1 id=existsun.1h6v.s9.8f3396550b16 from=translated src=- shape=9a906cbe vocab=c4792185
-/
theorem AlgebraicCurve.pDigits_existsUnique {K : Type u} {F : Type v} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by exact @_root_.P2MW.S_AlgebraicCurve_pDigits_existsUnique.solution K F _ _ _ _ p _ _ _ x _ t hdt g
