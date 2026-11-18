import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Repartitions
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_IsCurveOver
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.exists_pow_mul_mem_chartAlgFin_of_forall_place
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)]
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (x : F) (hx : ∀ v : Place K₀ F, j ∈ v.toValuationSubring → x ∈ v.toValuationSubring) :
    ∃ k : ℕ, algebraMap R F ϖ ^ k * x ∈ chartAlgFin R F j := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_pow_mul_mem_chartAlgFin_of_forall_place.solution R _ _ _ ϖ hϖ K₀ _ _ _ F _ _ _ _ j _ hFD x hx
