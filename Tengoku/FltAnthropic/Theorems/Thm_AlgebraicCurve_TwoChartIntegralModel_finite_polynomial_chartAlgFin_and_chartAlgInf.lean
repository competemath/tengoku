import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

/--
@isnad1 id=and.3h4v.s10.8d00c73e4db0 from=translated src=- shape=0ef6d554 vocab=497910ba
-/
theorem AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F) :
    (letI := (polynomialToChartFin R F j).toRingHom.toAlgebra
     Module.Finite (Polynomial R) ↥(chartAlgFin R F j)) ∧
    (letI := (polynomialToChartInf R F j).toRingHom.toAlgebra
     Module.Finite (Polynomial R) ↥(chartAlgInf R F j)) := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf.solution R _ _ _ _ K₀ _ _ _ F _ _ _ _ j _ htj hFD hsep
