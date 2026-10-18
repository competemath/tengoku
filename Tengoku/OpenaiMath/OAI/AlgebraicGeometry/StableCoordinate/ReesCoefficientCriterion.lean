import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.FilteredRees

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# Coefficientwise vanishing in an associated graded algebra

The principal Rees ideal `(T)` consists precisely of Laurent polynomials whose
coefficient in degree `d` belongs to `F (d-1)`.  This gives an actual
coefficientwise kernel test for the Rees model, including negative degrees.
-/

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]

end StableCoordinate.FilteredRees

end OAI
