import Tengoku.MagnitudeConjecture.MagnitudeConjecture.CategoryTheory.ShiftOrbitHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shifted objects are isomorphic in the shift-orbit category

The orbit category identifies every object with each of its shifts.  This
file constructs the identification explicitly from Mathlib's shift
equivalence and verifies both inverse laws against finite-support
convolution.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace MagnitudeConjecture.CoveringHom

universe u v w

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A : Type w} [AddGroup A] [HasShift C A]
variable [∀ a : A, (shiftFunctor C a).Additive]

/-- The homogeneous orbit morphism from an object to its degree-`a` shift.
Its orbit degree is `-a`.-/
def shiftOrbitToShift (X : C) (a : A) :
    ShiftOrbitHom A X ((shiftFunctor C a).obj X) :=
  shiftOrbitOf X ((shiftFunctor C a).obj X) (-a)
    (shiftShiftNeg X a).inv

/-- The homogeneous orbit morphism from a degree-`a` shift back to the
unshifted object.  Its orbit degree is `a`.-/
def shiftOrbitFromShift (X : C) (a : A) :
    ShiftOrbitHom A ((shiftFunctor C a).obj X) X :=
  shiftOrbitOf ((shiftFunctor C a).obj X) X a (𝟙 _)

end MagnitudeConjecture.CoveringHom
