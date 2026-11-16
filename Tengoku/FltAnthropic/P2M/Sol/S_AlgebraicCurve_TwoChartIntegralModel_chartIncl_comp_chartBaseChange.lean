import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_chartIncl_comp_chartBaseChange.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_chartIncl_comp_chartBaseChange

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]
    {S S' : Set F} (h : S ⊆ S') :
    (AlgebraicCurve.TwoChartIntegralModel.chartIncl R' F h).toRingHom.comp
        (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S) =
      (AlgebraicCurve.TwoChartIntegralModel.chartBaseChange R F R' S').comp
        (AlgebraicCurve.TwoChartIntegralModel.chartIncl R F h).toRingHom := by
  refine RingHom.ext fun x => Subtype.ext ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartIncl,
    AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange]
