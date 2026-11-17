import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatRank
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_comp_of_finrank_eq_const

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_isFinite_flat_and_finrank_pullback_fst_comp_eq_mul_of_finrank_eq_const

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
@isnad1 id=and.2h7v.s8.03eb3d0f2a20 from=translated src=- shape=deb1a2b4 vocab=0e09f541
-/
theorem solution
    {X Y Z : Scheme.{u}} (g : X ⟶ Z) (h : Y ⟶ Z)
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
    (m n : ℕ) (hg : ∀ z : Z, g.finrank z = m) (hh : ∀ z : Z, h.finrank z = n) :
    IsFinite (pullback.fst g h ≫ g) ∧ Flat (pullback.fst g h ≫ g) ∧ LocallyOfFinitePresentation (pullback.fst g h ≫ g) ∧
      ∀ z : Z, (pullback.fst g h ≫ g).finrank z = m * n := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun z => ?_⟩
  have hc : ∀ x : X, (pullback.fst g h).finrank x = n := fun x => by
    rw [Scheme.Hom.finrank_pullback_fst]; exact hh _
  rw [Scheme.Hom.finrank_comp_of_finrank_eq_const (pullback.fst g h) g n hc z, hg z, mul_comm]
