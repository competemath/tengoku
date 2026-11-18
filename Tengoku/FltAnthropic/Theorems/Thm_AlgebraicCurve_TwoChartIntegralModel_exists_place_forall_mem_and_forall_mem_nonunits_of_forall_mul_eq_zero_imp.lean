import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Repartitions
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_IsCurveOver
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

/--
@isnad1 id=ex.7h6v.s12.372b281ccdeb from=translated src=- shape=7b3a7050 vocab=e9f4bab8
-/
theorem AlgebraicCurve.TwoChartIntegralModel.exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (I : Ideal ↥(chartAlgFin R F f)) (hne : I ≠ ⊤) (hfI : jChartFin R F f ∈ I)
    (htor : ∀ y : ↥(chartAlgFin R F f) ⧸ I, algebraMap R (↥(chartAlgFin R F f) ⧸ I) ϖ * y = 0 → y = 0) :
    ∃ v : Place K₀ F, (∀ a : ↥(chartAlgFin R F f), (a : F) ∈ v.toValuationSubring) ∧
      ∀ a ∈ I, (a : F) ∈ v.toValuationSubring.nonunits := by exact @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp.solution R _ _ _ ϖ hϖ K₀ _ _ _ F _ _ _ _ f _ htf hFD hsep I hne hfI htor
