import Tengoku.Seed.Algebra.Homology.DerivedCategory.Ext.Basic
import Tengoku.Seed.CategoryTheory.Abelian.Projective.Dimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Projective dimension of a finite biproduct

A finite biproduct has projective dimension below a fixed bound when every
summand does.  This small generic lemma is shared by the weak-positivity and
Iyama-realization arguments.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace MagnitudeConjecture.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [HasFiniteBiproducts C]

/-- A finite biproduct has projective dimension below `d` if every summand
does.
@isnad1 id=hasproje.1h4v.s6.9403e8c4456e from=translated src=- shape=5acf8468 vocab=ecd00601
-/
theorem hasProjectiveDimensionLT_biproduct
    {J : Type*} [Fintype J] (F : J → C) (d : ℕ)
    (hF : ∀ j, HasProjectiveDimensionLT (F j) d) :
    HasProjectiveDimensionLT (⨁ F) d := by
  letI (j : J) : HasProjectiveDimensionLT (F j) d := hF j
  apply HasProjectiveDimensionLT.mk
  intro degree hdegree Y xi
  apply (Ext.biproductAddEquiv
    (biproduct.isBilimit F) Y degree).injective
  funext j
  simpa only [map_zero, Pi.zero_apply] using
    ((Ext.biproductAddEquiv (biproduct.isBilimit F) Y degree) xi j).eq_zero_of_hasProjectiveDimensionLT
      d hdegree

end MagnitudeConjecture.CategoryTheory
