import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.GradedDegreeCategory

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Simultaneous translation of graded shift labels -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
namespace MagnitudeConjecture.GradedCategory.HomGrading
universe u v w
variable {k : Type u} [Field k] {C : Type v} [Category.{w} C]
variable [Preadditive C] [Linear k C] (G : HomGrading k C)

/-- Translate all shift labels by the same integer.-/
def shiftFunctor (s : ℤ) : DegreeObject G ⥤ DegreeObject G where
  obj X := ⟨X.obj, X.degree + s⟩
  map f := ⟨f.val, by simpa only [add_sub_add_right_eq_sub] using f.property⟩
  map_id X := rfl
  map_comp f g := rfl

end MagnitudeConjecture.GradedCategory.HomGrading
