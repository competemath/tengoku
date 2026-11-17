import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt

set_option autoImplicit false

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ}
    (h : ρ.IsUnramifiedAt q) : ρ.IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  rw [h P hP σ hσ, LinearMap.charpoly_one, ρ.finrank_eq]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
