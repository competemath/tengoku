import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_jacobsonSpace_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=jacobson.0h3v.s5.eb3fa1e567a0 from=translated src=- shape=ff0a9f69 vocab=ffe5f61f
-/
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t] :
    JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace t
