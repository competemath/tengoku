import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Affine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

end StdCover

section StdCoverPullback

variable {A : Type u} [CommRing A] {n : ℕ}
variable {W : Scheme.{u}}
  (ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]

end StdCoverPullback

end ProjSpace

end AlgebraicGeometry

end
