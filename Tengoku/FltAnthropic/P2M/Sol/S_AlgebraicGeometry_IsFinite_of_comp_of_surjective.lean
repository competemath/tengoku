import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsFinite_of_comp_of_surjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsFinite_of_comp_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=isfinite.0h5v.s5.fd45502557bb from=translated src=- shape=2b6d9c58 vocab=02d3d0c0
-/
theorem solution {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Surjective f] [IsFinite (f ≫ g)] [LocallyOfFiniteType g] [IsSeparated g] : IsFinite g := by
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  haveI : IsProper g := IsProper.mk
  haveI : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    have hfin := (f ≫ g).finite_preimage_singleton z
    have hsub : g.base ⁻¹' {z} ⊆ f.base '' ((f ≫ g).base ⁻¹' {z}) := by
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, by simpa [Scheme.Hom.comp_apply] using hy, rfl⟩
    exact (hfin.image _).subset hsub
  exact IsFinite.of_isProper_of_locallyQuasiFinite g
