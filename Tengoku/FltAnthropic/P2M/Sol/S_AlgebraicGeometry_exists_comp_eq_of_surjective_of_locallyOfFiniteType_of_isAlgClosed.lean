import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_comp_eq_of_surjective_of_locallyOfFiniteType_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (y : Spec (.of K) ⟶ Y) :
    ∃ x : Spec (.of K) ⟶ X, x ≫ f = y := by

  have hne : Nonempty ↑(pullback f y) := by
    obtain ⟨z, -⟩ := (pullback.snd f y).surjective (IsLocalRing.closedPoint K)
    exact ⟨z⟩

  obtain ⟨-, s, hs, -⟩ :=
    (AlgebraicGeometry.dense_setOf_exists_section_of_isAlgClosed (pullback.snd f y)).nonempty
  exact ⟨s ≫ pullback.fst f y, by rw [Category.assoc, pullback.condition, reassoc_of% hs]⟩
