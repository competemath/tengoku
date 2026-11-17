import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isOpenImmersion_of_etale_of_universallyInjective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isOpenImmersion_of_etale_of_universallyInjective

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isopenim.0h3v.s4.3423be24c03a from=translated src=- shape=d492d1ea vocab=210ac28b
-/
theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] [UniversallyInjective f] :
    IsOpenImmersion f := by
  have hsurj : Surjective (Limits.pullback.diagonal f) := (UniversallyInjective.iff_diagonal f).mp ‹_›
  have h1 : IsOpenImmersion (Limits.pullback.diagonal f) := inferInstance
  have h2 : IsIso (Limits.pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨h1, hsurj⟩
  have h3 : Mono f := (Limits.pullback.isIso_diagonal_iff f).mp h2
  exact IsOpenImmersion.of_flat_of_mono f
