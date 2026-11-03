import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.AlmostSplitEquivalence
import Tengoku.Seed.CategoryTheory.Functor.EpiMono

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Almost-split morphisms under locally closed functors

For preservation of a right almost-split map, essential surjectivity is needed
only for objects carrying a nonzero nonsplit map to its endpoint.  The left
statement is dual.  These local conditions isolate the role of the first Hom
neighborhoods in the covering-control argument, while minimality of either
map is preserved by full faithfulness alone.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open QuotientSubmoduleEquidistribution

namespace MagnitudeConjecture

universe u v u' v'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- Every object relevant to testing right almost-splitness at `F.obj Y` lies
in the essential image.  The zero map is excluded because it factors
trivially and needs no object lift.-/
def IsLocallyRightObjectClosedAt (F : C ⥤ D) (Y : C) : Prop :=
  ∀ (W : D) (g : W ⟶ F.obj Y),
    g ≠ 0 → ¬ IsSplitEpi g →
      ∃ V : C, Nonempty (F.obj V ≅ W)

/-- Every object relevant to testing left almost-splitness at `F.obj X` lies
in the essential image.-/
def IsLocallyLeftObjectClosedAt (F : C ⥤ D) (X : C) : Prop :=
  ∀ (W : D) (g : F.obj X ⟶ W),
    g ≠ 0 → ¬ IsSplitMono g →
      ∃ V : C, Nonempty (F.obj V ≅ W)

end MagnitudeConjecture
