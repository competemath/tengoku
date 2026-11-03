import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.CategoricalRadical
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.HomIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The categorical radical as an additive Hom ideal

The Jacobson condition `IsRadicalMorphism f` is closed under addition,
negation, and arbitrary composition.  Consequently it defines a canonical
two-sided additive Hom ideal in every preadditive category.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.CategoricalRadical

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The zero morphism is radical.
@isnad1 id=isradica.0h3v.s5.1ae144b51e30 from=translated src=- shape=9ca04576 vocab=342e06c2
-/
theorem isRadicalMorphism_zero {X Y : C} :
    IsRadicalMorphism (0 : X ⟶ Y) := by
  intro g
  simpa using inferInstanceAs (IsIso (𝟙 X))

/-- The negative of a radical morphism is radical.
@isnad1 id=isradica.1h4v.s6.1560d0616b72 from=translated src=- shape=534669ed vocab=8f8353dc
-/
theorem isRadicalMorphism_neg {X Y : C} {f : X ⟶ Y}
    (hf : IsRadicalMorphism f) :
    IsRadicalMorphism (-f) := by
  intro g
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg,
    sub_neg_eq_add] using hf (-g)

/-- The sum of two radical morphisms is radical.
@isnad1 id=isradica.2h5v.s7.5e9ee669702a from=translated src=- shape=dc374308 vocab=9c1111b8
-/
theorem isRadicalMorphism_add {X Y : C} {f r : X ⟶ Y}
    (hf : IsRadicalMorphism f) (hr : IsRadicalMorphism r) :
    IsRadicalMorphism (f + r) := by
  intro g
  let a : X ⟶ X := 𝟙 X - f ≫ g
  letI : IsIso a := hf g
  let b : X ⟶ X := 𝟙 X - r ≫ (g ≫ inv a)
  letI : IsIso b := hr (g ≫ inv a)
  have hfactor :
      𝟙 X - (f + r) ≫ g = b ≫ a := by
    dsimp only [a, b]
    simp only [Preadditive.add_comp, Preadditive.sub_comp,
      Category.id_comp, Category.assoc]
    rw [IsIso.inv_hom_id, Category.comp_id]
    abel
  rw [hfactor]
  infer_instance

/-- The canonical categorical Jacobson radical Hom ideal.-/
def homIdeal : CategoricalIdeal.HomIdeal C where
  hom _ _ :=
    { carrier := {f | IsRadicalMorphism f}
      zero_mem' := isRadicalMorphism_zero
      add_mem' := fun hf hg ↦ isRadicalMorphism_add hf hg
      neg_mem' := fun hf ↦ isRadicalMorphism_neg hf }
  precomp := fun f _ hg ↦ isRadicalMorphism_precomp f hg
  postcomp := fun g hf ↦ isRadicalMorphism_postcomp g hf

/--
@isnad1 id=iff.0h4v.s7.958c737bb1f8 from=translated src=- shape=4e9ab829 vocab=4eb797ae
-/
@[simp]
theorem mem_homIdeal_iff {X Y : C} (f : X ⟶ Y) :
    f ∈ (homIdeal : CategoricalIdeal.HomIdeal C).hom X Y ↔
      IsRadicalMorphism f :=
  Iff.rfl

end QuotientSubmoduleEquidistribution.CategoricalRadical
