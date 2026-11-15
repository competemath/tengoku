import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_base_genericPoint_eq_genericPoint_of_subset_range

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {Z X : Scheme.{u}} [IrreducibleSpace ↥Z] [IsIntegral X] (q : Z ⟶ X) (U : X.Opens)
    (hU : (U : Set ↥X).Nonempty) (hsub : (U : Set ↥X) ⊆ Set.range q.base) :
    q.base (genericPoint ↥Z) = genericPoint ↥X := by
  have h1 : IsGenericPoint (q.base (genericPoint ↥Z)) (closure (q.base '' (⊤ : Set ↥Z))) :=
    (genericPoint_spec ↥Z).image q.continuous
  have hdense : closure (q.base '' (⊤ : Set ↥Z)) = (⊤ : Set ↥X) := by
    apply Set.eq_univ_of_univ_subset
    have hUd : Dense (U : Set ↥X) := U.isOpen.dense hU
    rw [← hUd.closure_eq]
    apply closure_minimal _ isClosed_closure
    refine hsub.trans ?_
    rw [Set.top_eq_univ, Set.image_univ]
    exact subset_closure
  rw [hdense] at h1
  exact h1.eq (genericPoint_spec ↥X)
