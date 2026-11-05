module

public import Tengoku.Seed.AlgebraicGeometry.Morphisms.FlatRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} (f : X ⟶ S)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f]

/--
@isnad1 id=eq.0h5v.s6.7195c0bea75c from=translated src=- shape=e0b34f47 vocab=cc36366e
-/
lemma finrank_eq_const_of_preconnectedSpace [PreconnectedSpace Y] (y y' : Y) :
    f.finrank y = f.finrank y' := by
  apply IsLocallyConstant.apply_eq_of_preconnectedSpace
  apply f.isLocallyConstant_finrank

end

end AlgebraicGeometry
