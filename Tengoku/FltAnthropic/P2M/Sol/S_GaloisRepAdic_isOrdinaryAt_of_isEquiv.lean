import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_isEquiv.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isEquiv

open scoped TensorProduct

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (DetIsCyclotomic IsOrdinaryAt IsUnipotentOnInertiaAt IsUnramifiedAt det baseChangeAlong Equiv IsEquiv ρ V)
namespace LCSol
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

/--
@isnad1 id=isordina.2h4v.s5.678a635e5bf8 from=translated src=- shape=fadfb841 vocab=baefa325
-/
theorem isOrdinaryAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsOrdinaryAt p) : ρ₂.IsOrdinaryAt p := by
  obtain ⟨e⟩ := e
  intro P hP
  obtain ⟨L, ⟨b, hL⟩, hstab, hinert⟩ := h P hP
  refine ⟨L.map (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V), ⟨b.map e.toLinearEquiv, ?_⟩, ?_, ?_⟩
  · rw [hL, Submodule.map_span, Set.image_singleton, Module.Basis.map_apply,
      LinearEquiv.coe_coe]
  · intro σ hσ w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    rw [LinearEquiv.coe_coe, ← e.map_apply]
    exact Submodule.mem_map_of_mem (hstab σ hσ v hv)
  · intro σ hσ w
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
    rw [← e.map_apply, ← map_sub]
    exact Submodule.mem_map_of_mem (hinert σ hσ v)

end GaloisRepAdic.LCSol

/--
@isnad1 id=isordina.2h4v.s5.678a635e5bf8 from=translated src=- shape=fadfb841 vocab=baefa325
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsOrdinaryAt p) : ρ₂.IsOrdinaryAt p :=
  GaloisRepAdic.LCSol.isOrdinaryAt_of_isEquiv e h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
