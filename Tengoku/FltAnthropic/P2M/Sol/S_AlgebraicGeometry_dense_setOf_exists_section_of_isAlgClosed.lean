import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=dense.0h3v.s8.7e5942437efd from=translated src=- shape=e4b80bc7 vocab=03288ed1
-/
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] :
    Dense {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆
      {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} :=
    fun x hx => ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx,
      pointOfClosedPoint_apply f x hx _⟩
  exact Dense.mono hsub (dense_iff_closure_eq.mpr (closure_closedPoints (X := X)))
