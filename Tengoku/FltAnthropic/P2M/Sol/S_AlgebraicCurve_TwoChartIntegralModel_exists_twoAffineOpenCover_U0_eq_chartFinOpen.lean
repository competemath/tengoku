import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_twoAffineOpenCover_U0_eq_chartFinOpen

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.AlgebraicCurve.TwoChartIntegralModel

namespace AlgebraicCurve
export _root_.AlgebraicCurve (TwoChartIntegralModel TwoChartIntegralModel.isAffineOpen_chartFinOpen TwoChartIntegralModel.isAffineOpen_chartInfOpen TwoChartIntegralModel.twoChartCover)
namespace TwoChartIntegralModel
export _root_.AlgebraicCurve.TwoChartIntegralModel (XFin XInf XMid fFin fInf ιFin ιInf glue_condition chartFinOpen chartInfOpen isAffineOpen_chartFinOpen isAffineOpen_chartInfOpen twoChartCover)
namespace CoverAux
open _root_.AlgebraicCurve.TwoChartIntegralModel open _root_.AlgebraicCurve

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

/--
@isnad1 id=iff.0h5v.s10.48d937aa63bc from=translated src=- shape=947d44f4 vocab=fdf73688
-/
theorem ιFin_eq_ιInf_iff (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · rcases fi with _ | _
      rcases fj with _ | _
      exact ⟨w, h₁, h₂⟩
    · rcases fj with _ | _
    · rcases fi with _ | _
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w = (fInf R F j ≫ ιInf R F j).base w
    rw [glue_condition]

/--
@isnad1 id=eq.0h3v.s7.eec5588f8d32 from=translated src=- shape=334a2c34 vocab=8866f4eb
-/
theorem chartFinOpen_inf_chartInfOpen :
    chartFinOpen R F j ⊓ chartInfOpen R F j = (fFin R F j ≫ ιFin R F j).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_inf, chartFinOpen, chartInfOpen, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
  ext x
  constructor
  · rintro ⟨⟨x₀, rfl⟩, ⟨xi, hxi⟩⟩
    obtain ⟨w, hw, -⟩ := (ιFin_eq_ιInf_iff R F j x₀ xi).mp hxi.symm
    refine ⟨w, ?_⟩
    rw [Scheme.Hom.comp_apply]
    change (ιFin R F j).base ((fFin R F j).base w) = (ιFin R F j).base x₀
    rw [hw]
  · rintro ⟨w, rfl⟩
    refine ⟨⟨(fFin R F j).base w, ?_⟩, ⟨(fInf R F j).base w, ?_⟩⟩
    · rw [Scheme.Hom.comp_apply]
    · change (ιInf R F j) ((fInf R F j) w) = (fFin R F j ≫ ιFin R F j) w
      rw [glue_condition, Scheme.Hom.comp_apply]

end AlgebraicCurve.TwoChartIntegralModel.CoverAux

/--
@isnad1 id=ex.0h3v.s6.8c1adb5fc535 from=translated src=- shape=25ad4efb vocab=6b479a65
-/
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    ∃ 𝒱 : (AlgebraicCurve.TwoChartIntegralModel R F j).TwoAffineOpenCover,
      𝒱.U0 = chartFinOpen R F j ∧ 𝒱.U1 = chartInfOpen R F j :=
  ⟨{ U0 := chartFinOpen R F j
     U1 := chartInfOpen R F j
     isAffineOpen_U0 := AlgebraicCurve.TwoChartIntegralModel.isAffineOpen_chartFinOpen R F j
     isAffineOpen_U1 := AlgebraicCurve.TwoChartIntegralModel.isAffineOpen_chartInfOpen R F j
     sup_eq_top := AlgebraicCurve.TwoChartIntegralModel.twoChartCover R F j
     isAffineOpen_inf := by
       rw [AlgebraicCurve.TwoChartIntegralModel.CoverAux.chartFinOpen_inf_chartInfOpen]
       exact isAffineOpen_opensRange _ }, rfl, rfl⟩
