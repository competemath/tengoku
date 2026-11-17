import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_surjective_specMap_of_surjective_of_ker_le_nilradical

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hker : RingHom.ker f ≤ nilradical R) :
    Surjective (Spec.map (CommRingCat.ofHom f)) := by
  have h := PrimeSpectrum.isHomeomorph_comap f (fun x => ⟨1, one_pos, by simpa using hf x⟩) hker
  exact ⟨fun x => by
    obtain ⟨y, hy⟩ := h.surjective x
    exact ⟨y, hy⟩⟩
