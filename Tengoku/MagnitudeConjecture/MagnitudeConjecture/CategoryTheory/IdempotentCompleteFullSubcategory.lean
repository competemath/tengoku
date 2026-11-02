import Tengoku.Seed.CategoryTheory.Idempotents.Basic
import Tengoku.Seed.CategoryTheory.ObjectProperty.Retract

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Idempotent completeness of retract-stable full subcategories

A full subcategory cut out by a retract-stable object property inherits
idempotent completeness from its ambient category.  The splitting object is
the ambient retract selected by the idempotent.
-/

set_option autoImplicit false

open CategoryTheory

namespace MagnitudeConjecture

universe u v

/-- A retract-stable full subcategory of an idempotent-complete category is
idempotent-complete.-/
theorem isIdempotentComplete_fullSubcategory_of_stableUnderRetracts
    {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    [P.IsStableUnderRetracts] [IsIdempotentComplete C] :
    IsIdempotentComplete P.FullSubcategory := by
  refine ⟨?_⟩
  intro X p hp
  let U := P.ι
  have hp' : U.map p ≫ U.map p = U.map p := by
    simpa only [U.map_comp, U.map_id] using congrArg U.map hp
  obtain ⟨Y, i, r, hir, hri⟩ :=
    IsIdempotentComplete.idempotents_split (U.obj X) (U.map p) hp'
  let Y' : P.FullSubcategory :=
    ⟨Y, P.prop_of_retract ⟨i, r, hir⟩ X.property⟩
  refine ⟨Y', ObjectProperty.homMk i, ObjectProperty.homMk r, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    exact hir
  · apply ObjectProperty.hom_ext
    exact hri

end MagnitudeConjecture
