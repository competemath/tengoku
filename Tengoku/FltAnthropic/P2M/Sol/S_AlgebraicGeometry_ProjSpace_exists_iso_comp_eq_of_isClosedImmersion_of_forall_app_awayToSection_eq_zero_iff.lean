import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_app_awayToSection_eq_zero_of_app_awayToSection_eq_zero
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_iso_comp_eq_of_isClosedImmersion_of_forall_app_awayToSection_eq_zero_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_iso_comp_eq_of_isClosedImmersion_of_forall_app_awayToSection_eq_zero_iff

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

namespace ClosedChartwise

variable {A : Type} [CommRing A] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/--
@isnad1 id=mem.0h3v.s8.a82284bced7b from=translated src=- shape=8980d550 vocab=7d23f883
-/
theorem X_mem_one (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) A) ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X A j)

end ClosedChartwise
