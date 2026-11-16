import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem solution
    {X : Scheme.{u}} (U : X.Opens) (T : Type u) [CommRing T] [IsLocalRing T]
    (f : Spec (CommRingCat.of T) ⟶ X) (hx : f.base (IsLocalRing.closedPoint T) ∈ U) :
    Set.range f.base ⊆ (U : Set ↥X) := by
  rintro _ ⟨p, rfl⟩
  have hsp : p ⤳ IsLocalRing.closedPoint T :=
    (PrimeSpectrum.le_iff_specializes p (IsLocalRing.closedPoint T)).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  exact (hsp.map f.base.hom.continuous).mem_open U.isOpen hx
