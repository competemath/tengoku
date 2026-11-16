import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

/--
@isnad1 id=and.0h5v.s6.6c1a10681fb4 from=translated src=- shape=921ae4d7 vocab=a848906b
-/
theorem solution
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) (g : X ⟶ Y) [IsClosedImmersion i] [Etale g]
    [Flat (i ≫ g)] [LocallyOfFinitePresentation (i ≫ g)] :
    IsOpenImmersion i ∧ Etale (i ≫ g) := by

  have hmono : Mono i := inferInstance
  have hdiag : IsOpenImmersion (Limits.pullback.diagonal i) := inferInstance
  have hi : FormallyUnramified i := inferInstance
  have hg : FormallyUnramified g := inferInstance
  have hig : FormallyUnramified (i ≫ g) := MorphismProperty.comp_mem _ i g hi hg
  have het : Etale (i ≫ g) := Etale.of_formallyUnramified_of_flat (f := i ≫ g)
  have heti : Etale i := Etale.of_comp i g
  have hflat : Flat i := (Etale.iff_flat_and_formallyUnramified.mp heti).1
  have hlfp : LocallyOfFinitePresentation i := (Etale.iff_flat_and_formallyUnramified.mp heti).2.2
  exact ⟨IsOpenImmersion.of_flat_of_mono i, het⟩
