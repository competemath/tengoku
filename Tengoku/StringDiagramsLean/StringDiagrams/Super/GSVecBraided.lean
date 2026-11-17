import Tengoku.StringDiagramsLean.StringDiagrams.Super.GSVecMonoidal
import Tengoku.StringDiagramsLean.StringDiagrams.Super.SVecBraided

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The symmetric braiding of graded superspaces

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (before
Definition 6.1): the category `GSVec̲` of graded superspaces and degree-preserving even linear
maps "is a symmetric monoidal category with `(V ⊗ W)ₙ = ⨁_{r+s=n} Vᵣ ⊗ Wₛ`, and the same
braiding as in `SVec`". Thus the sign of the braiding depends only on the parities, not on the
`ℤ`-degrees: `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v` for `v`, `w` of parities `|v|`, `|w|` and
arbitrary degrees (`GSVec.braiding_hom_tmul`).

* The braiding `SVec.braidingMap` of `StringDiagrams.Super.SVecBraided` has degree zero
  (`GradedSuperspace.braidingMap_mem_degHom`): it maps `Vᵣ ⊗ Wₛ` to `Wₛ ⊗ Vᵣ`.
* Hence `GSVec k` is a braided monoidal supercategory
  (`GSVec.instBraidedMonoidalSupercategory`), with braiding of degree zero
  (`GSVec.braiding_hom_mem_degree`) and symmetric (`GSVec.braiding_hom_comp_braiding_hom`).
* For a graded monoidal supercategory `C`, the morphisms of degree zero form a monoidal
  supercategory (`GradedSupercategory.DegreeZero.instMonoidalSupercategory`), so that the
  underlying category `GUnderlying R C` of even morphisms of degree zero is a monoidal category.
  For `GSVec k` the braiding restricts to the degree-zero morphisms
  (`GSVec.instBraidedMonoidalSupercategoryDegreeZero`), and the paper's `GSVec̲ =
  GradedSupercategory.GUnderlying k (GSVec k)` is a symmetric monoidal category
  (`GSVec.instSymmetricCategoryGUnderlying`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory TensorProduct

/-! ## The monoidal supercategory of morphisms of degree zero -/

namespace GradedSupercategory.DegreeZero

universe w w₁ w₂

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C] [MonoidalCategoryStruct C]
  [MonoidalSupercategory R C] [GradedMonoidalSupercategory R C]

/-- The monoidal structure of the morphisms of degree zero of a graded monoidal
supercategory.-/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (DegreeZero R C) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ f := ⟨X.obj ◁ f.1, GradedMonoidalSupercategory.whiskerLeft_mem_degree _ f.2⟩
  whiskerRight f Y := ⟨f.1 ▷ Y.obj, GradedMonoidalSupercategory.whiskerRight_mem_degree _ f.2⟩
  tensorHom f g :=
    ⟨f.1 ⊗ₘ g.1, by simpa using GradedMonoidalSupercategory.tensorHom_mem_degree f.2 g.2⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := isoMk (α_ X.obj Y.obj Z.obj)
    (GradedMonoidalSupercategory.associator_hom_mem_degree _ _ _)
  leftUnitor X := isoMk (λ_ X.obj) (GradedMonoidalSupercategory.leftUnitor_hom_mem_degree _)
  rightUnitor X := isoMk (ρ_ X.obj) (GradedMonoidalSupercategory.rightUnitor_hom_mem_degree _)

/--
@isnad1 id=eq.0h4v.s6.1577a754f165 from=translated src=- shape=8301f442 vocab=02cf0bdb
-/
@[simp] theorem tensorObj_obj (X Y : DegreeZero R C) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

/--
@isnad1 id=eq.0h2v.s6.7df8e14e1047 from=translated src=- shape=b1f6cc30 vocab=7db2dd13
-/
@[simp] theorem tensorUnit_obj : (𝟙_ (DegreeZero R C)).obj = 𝟙_ C := rfl

/--
@isnad1 id=eq.0h6v.s10.2413032476e5 from=translated src=- shape=c48e1856 vocab=6ade504e
-/
@[simp] theorem whiskerLeft_val (X : DegreeZero R C) {Y Y' : DegreeZero R C} (f : Y ⟶ Y') :
    (X ◁ f).1 = X.obj ◁ f.1 := rfl

/--
@isnad1 id=eq.0h6v.s10.3098f61eeb93 from=translated src=- shape=1e12004b vocab=473d301e
-/
@[simp] theorem whiskerRight_val {X X' : DegreeZero R C} (f : X ⟶ X') (Y : DegreeZero R C) :
    (f ▷ Y).1 = f.1 ▷ Y.obj := rfl

/--
@isnad1 id=eq.0h8v.s10.63ee27dfdb62 from=translated src=- shape=1523f712 vocab=7b237975
-/
@[simp] theorem tensorHom_val {X X' Y Y' : DegreeZero R C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g).1 = f.1 ⊗ₘ g.1 := rfl

/--
@isnad1 id=eq.0h5v.s11.6108086e684c from=translated src=- shape=9206a14d vocab=f40c8b58
-/
@[simp] theorem associator_hom_val (X Y Z : DegreeZero R C) :
    (α_ X Y Z).hom.1 = (α_ X.obj Y.obj Z.obj).hom := rfl

/--
@isnad1 id=eq.0h3v.s10.9e40e6defb41 from=translated src=- shape=29205b3f vocab=24437ada
-/
@[simp] theorem leftUnitor_hom_val (X : DegreeZero R C) : (λ_ X).hom.1 = (λ_ X.obj).hom := rfl

/--
@isnad1 id=eq.0h3v.s10.a4900a9babc3 from=translated src=- shape=804d87ba vocab=7eb87171
-/
@[simp] theorem rightUnitor_hom_val (X : DegreeZero R C) : (ρ_ X).hom.1 = (ρ_ X.obj).hom := rfl

end GradedSupercategory.DegreeZero

universe u

variable {k : Type u} [CommRing k]

/-! ## The braiding has degree zero -/

namespace GradedSuperspace

end GradedSuperspace

/-! ## The braided monoidal supercategory `GSVec` -/

namespace GSVec

open GradedSuperspace GradedSubcategory

/-! ## The symmetric monoidal category `GSVec̲` -/

end GSVec

end StringDiagrams

end
