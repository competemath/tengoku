import Tengoku.Seed.AlgebraicGeometry.Morphisms.Flat
import Tengoku.Seed.RingTheory.Flat.TorsionFree
import Tengoku.Seed.RingTheory.DedekindDomain.Basic
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Theorems.Thm_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (TwoChartIntegralModel)
namespace TwoChartIntegralModel
export _root_.AlgebraicCurve.TwoChartIntegralModel (chartAlg adjoin_le_chartAlg chartAlgFin chartAlgInf)
open _root_.AlgebraicCurve.TwoChartIntegralModel open _root_.AlgebraicCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

omit [Fact (j ≠ 0)] in

theorem isIntegrallyClosed_chartAlg_impl (S : Set F) : IsIntegrallyClosed (chartAlg R F S) := by
  let R₀ : Subalgebra R F := Algebra.adjoin R S
  let A : Subalgebra R F := chartAlg R F S
  have hRA : R₀ ≤ A := adjoin_le_chartAlg R F S
  letI : Algebra R₀ A := (Subalgebra.inclusion hRA).toRingHom.toAlgebra
  haveI : IsScalarTower R₀ A F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral R₀ A := by
    refine ⟨fun a => ?_⟩
    have ha : IsIntegral R₀ (a : F) := a.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R₀ A F) Subtype.val_injective).mp ha
  haveI : FaithfulSMul A F := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact Subtype.val_injective
  haveI : IsIntegrallyClosedIn A F := by
    refine (isIntegrallyClosedIn_iff).mpr ⟨Subtype.val_injective, fun {x} hx => ?_⟩
    have hx' : IsIntegral R₀ x := isIntegral_trans x hx
    exact ⟨⟨x, hx'⟩, rfl⟩
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn_of_faithfulSMul A F

end AlgebraicCurve.TwoChartIntegralModel

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.AlgebraicCurve.TwoChartIntegralModel _root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg.AlgebraicCurve.TwoChartIntegralModel in
theorem solution.{u} (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (S : Set F) :
    IsIntegrallyClosed ↥(chartAlg R F S) :=
  AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg_impl R F S
