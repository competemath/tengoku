import Tengoku.Seed.CategoryTheory.Category.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Small congruence lemmas for categorical composition
-/

set_option autoImplicit false

namespace MagnitudeConjecture

open CategoryTheory

universe v u

/-- Precomposition preserves equality of morphisms.  Naming this generic
operation prevents downstream elaboration from expanding a large concrete
morphism family inside `congrArg`.
@isnad1 id=eq.1h7v.s6.b38ff82a590d from=translated src=- shape=f276df70 vocab=3864ac9d
-/
theorem precomp_congr
    {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) {g h : Y ⟶ Z} (e : g = h) :
    f ≫ g = f ≫ h :=
  congrArg (fun t ↦ f ≫ t) e

/-- An equality of a two-step composite remains true after one further
precomposition, with reassociation performed generically.
@isnad1 id=eq.1h9v.s6.a4f270976e6a from=translated src=- shape=2a29b3e2 vocab=3864ac9d
-/
theorem assoc_comp_congr
    {C : Type u} [Category.{v} C] {W X Y Z : C}
    (f : W ⟶ X) {g : X ⟶ Y} {h : Y ⟶ Z} {l : X ⟶ Z}
    (e : g ≫ h = l) :
    (f ≫ g) ≫ h = f ≫ l :=
  (Category.assoc _ _ _).trans (precomp_congr f e)

end MagnitudeConjecture
