import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RingHom export _root_.RingHom (Smooth IsStandardSmoothOfRelativeDimension locally_of toMorphismProperty_respectsIso_iff isStandardSmoothOfRelativeDimension_respectsIso locally_respectsIso Locally toMorphismProperty IsStandardSmooth toAlgebra) namespace IsStandardSmooth export _root_.RingHom.IsStandardSmooth (toAlgebra smooth) end RingHom.IsStandardSmooth
open scoped _root_.RingHom _root_.RingHom.IsStandardSmooth in

theorem RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3
    {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S} (h : φ.IsStandardSmooth) :
    ∃ n : ℕ, φ.IsStandardSmoothOfRelativeDimension n := by
  letI := φ.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := h.out
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨d, hd⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_gc3 hstd
  refine ⟨V, d, hx, ?_⟩

  have hres : SmoothOfRelativeDimension d (f.resLE U V e) := by
    haveI : IsAffine V := hV
    haveI : IsAffine U := hU
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension d)]
    have := (RingHom.toMorphismProperty_respectsIso_iff.mp
      (RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d))))
    refine ((MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d))) (arrowResLEAppIso f U V e)).mpr ?_)
    exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := d)) _ hd
  rw [← Scheme.Hom.resLE_comp_ι f e]
  have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
  simpa using this
