import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_TwoChartModel
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)] :
    ∃ e : ModularCurve.TwoChartModel A K j ≅ AlgebraicCurve.TwoChartIntegralModel A K j,
      e.hom ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A K j = ModularCurve.TwoChart.modelTo A K j ∧
      ModularCurve.TwoChart.ιFin A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιFin A K j ∧
      ModularCurve.TwoChart.ιInf A K j ≫ e.hom = AlgebraicCurve.TwoChartIntegralModel.ιInf A K j :=
  ⟨Iso.refl _, Category.id_comp _, Category.comp_id _, Category.comp_id _⟩

