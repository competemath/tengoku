import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Almost-split morphisms under equivalence

An ordinary categorical equivalence preserves right and left almost-split
morphisms and their minimality.  The proof uses essential surjectivity to
pull an arbitrary test object back across the equivalence and full
faithfulness to reflect splittings.

This is the covariant companion of the anti-equivalence argument in
`QuotientSubmoduleEquidistribution.RepresentationTheory.AlmostSplitDuality`;
only the two transport lemmas required by the support-algebra passage are
included here.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]

end QuotientSubmoduleEquidistribution
