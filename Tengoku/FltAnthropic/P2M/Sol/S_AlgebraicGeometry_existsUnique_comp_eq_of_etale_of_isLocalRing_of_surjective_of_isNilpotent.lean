import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_existsUnique_comp_eq_of_etale_of_isLocalRing_of_surjective_of_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace TanLift8

variable {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]

end TanLift8

namespace TanLift8

open IsLocalRing

variable {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]

omit [IsLocalRing C] in
theorem specializes_of_eq {X : Scheme.{u}} {x y : ↥X} (h : x = y) : x ⤳ y := h ▸ specializes_rfl

end TanLift8

namespace TanLift10

end TanLift10
