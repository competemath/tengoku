import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg

set_option autoImplicit false

universe u

/--
@isnad1 id=flat.1h3v.s8.7ffc6a6ba351 from=translated src=- shape=27f57e3d vocab=512c42b7
-/
theorem solution
    {R F : Type u} [CommRing R] [IsDomain R] [IsBezout R] [Field F] [Algebra R F]
    (hRF : Function.Injective (algebraMap R F)) (S : Set F) :
    Module.Flat R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) := by
  have hinj : Function.Injective (algebraMap R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S)) :=
    fun a b hab => hRF (congrArg Subtype.val hab)
  haveI : Module.IsTorsionFree R ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F S) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

