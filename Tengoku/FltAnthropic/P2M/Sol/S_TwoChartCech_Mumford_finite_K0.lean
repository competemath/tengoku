import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_MumfordTruncation
import Tengoku.Seed.RingTheory.Noetherian.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_TwoChartCech_Mumford_finite_K0.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_TwoChartCech_Mumford_finite_K0

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech
export _root_.TwoChartCech (Mumford.K0)
namespace Mumford
export _root_.TwoChartCech.Mumford (rank lift K0 mem_K0_iff dK ι0 dK_apply ι0_apply)
open _root_.TwoChartCech.Mumford open _root_.TwoChartCech

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

def kerToK0 : LinearMap.ker d →ₗ[R] K0 d :=
  LinearMap.codRestrict (K0 d)
    ((LinearMap.inl R C0 (Fin (rank d) → R)).comp (LinearMap.ker d).subtype)
    (fun ⟨x, hx⟩ => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.inl_apply,
        LinearMap.coprod_apply, map_zero, add_zero]
      exact hx)

def kerEquiv : LinearMap.ker (dK d) ≃ₗ[R] LinearMap.ker d := by
  refine LinearEquiv.ofLinearMap
    (LinearMap.codRestrict (LinearMap.ker d) ((ι0 d).comp (LinearMap.ker (dK d)).subtype) ?_)
    (LinearMap.codRestrict (LinearMap.ker (dK d)) (kerToK0 d) (fun x => by
      simp only [LinearMap.mem_ker, dK_apply]; rfl))
    ?_ ?_
  · rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hxv' : d x + lift d v = 0 := (mem_K0_iff d _).mp hxv
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, ι0_apply]
    simpa [hv', map_zero, add_zero] using hxv'
  · apply LinearMap.ext; rintro ⟨x, hx⟩; rfl
  · apply LinearMap.ext; rintro ⟨⟨⟨x, v⟩, hxv⟩, hv⟩
    have hv' : v = 0 := (LinearMap.mem_ker).mp hv
    apply Subtype.ext; apply Subtype.ext
    show ((x, 0) : C0 × _) = (x, v)
    rw [hv']

end TwoChartCech.Mumford

open _root_.TwoChartCech.Mumford _root_.P2MW.S_TwoChartCech_Mumford_finite_K0.TwoChartCech.Mumford in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Finite R (TwoChartCech.Mumford.K0 d) := by
  haveI hker : Module.Finite R (LinearMap.ker (dK d)) := Module.Finite.equiv (kerEquiv d).symm
  haveI hquot : Module.Finite R (K0 d ⧸ LinearMap.ker (dK d)) := by
    haveI : Module.Finite R (LinearMap.range (dK d)) := inferInstance
    exact Module.Finite.equiv (dK d).quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (dK d))

end
