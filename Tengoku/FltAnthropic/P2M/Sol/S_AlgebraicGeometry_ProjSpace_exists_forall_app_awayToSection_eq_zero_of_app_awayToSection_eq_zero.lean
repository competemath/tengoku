import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace KcR4S220
namespace ChartExtension

open HomogeneousLocalization TopologicalSpace Opposite

section Geometry

variable (A : Type) [CommRing A] (n : ℕ)

end Geometry

section Fractions

variable {A : Type} [CommRing A] (n : ℕ)

end Fractions

section Main

variable {A : Type} [CommRing A] (n : ℕ) {Z : Scheme.{0}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

end Main

end KcR4S220.ChartExtension

end
