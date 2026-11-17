import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isEquiv

open scoped TensorProduct

namespace GaloisRepAdic
export _root_.Tengoku.FltAnthropic.GaloisRepAdic (DetIsCyclotomic IsOrdinaryAt IsUnipotentOnInertiaAt IsUnramifiedAt det baseChangeAlong Equiv IsEquiv ρ V)
namespace LCSol
open _root_.Tengoku.FltAnthropic.GaloisRepAdic

variable {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]

theorem Equiv.eq_conj {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₂.ρ σ = e.toLinearEquiv.conj (ρ₁.ρ σ) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearEquiv.conj_apply_apply, e.map_apply, LinearEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h5v.s11.7c08d2bbfe11 from=translated src=- shape=be0b1f20 vocab=987dc9ec
-/
theorem Equiv.charpoly_apply_eq {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₂.ρ σ).charpoly = (ρ₁.ρ σ).charpoly := by
  rw [Equiv.eq_conj e σ, LinearEquiv.charpoly_conj]

/--
@isnad1 id=isunipot.2h4v.s5.b1ec5e7ded9f from=translated src=- shape=fadfb841 vocab=c1cc0570
-/
theorem isUnipotentOnInertiaAt_of_isEquiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnipotentOnInertiaAt q) : ρ₂.IsUnipotentOnInertiaAt q := by
  obtain ⟨e⟩ := e
  intro P hP σ hσ
  rw [Equiv.charpoly_apply_eq e σ]
  exact h P hP σ hσ

end GaloisRepAdic.LCSol

/--
@isnad1 id=isunipot.2h4v.s5.b1ec5e7ded9f from=translated src=- shape=fadfb841 vocab=c1cc0570
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnipotentOnInertiaAt q) : ρ₂.IsUnipotentOnInertiaAt q :=
  GaloisRepAdic.LCSol.isUnipotentOnInertiaAt_of_isEquiv e h

-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
