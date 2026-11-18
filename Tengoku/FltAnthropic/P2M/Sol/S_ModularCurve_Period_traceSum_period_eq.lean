import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PeriodMap
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PeriodTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_Period_traceSum_period_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_Period_traceSum_period_eq

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve.Period

/--
@isnad1 id=eq.1h4v.s11.8d2ad92acd5f from=translated src=- shape=5b378bbc vocab=1c485861
-/
theorem solution :
    ∀ {Γ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
      {F : UpperHalfPlane → ℂ} [inst : Fintype (↥Γ ⧸ Δ.subgroupOf Γ)]
      (hF : ModularCurve.Period.IsEquivariantPrimitive Δ F) (γ : ↥Γ),
      (ModularCurve.Period.IsEquivariantPrimitive.traceSum hF).period γ =
        ∑ q, hF.period (ModularCurve.Period.transferElt γ q) := by
  intro Γ Δ F inst hF γ
  rw [← IsEquivariantPrimitive.sub_eq_period hF.traceSum γ UpperHalfPlane.I]
  exact sum_traceRep_smul_sub hF γ UpperHalfPlane.I

