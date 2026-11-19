/-
Reused under MIT from CollinYuanjieRen/awards, commit
b8bb4f7803f921a7970abc880291ad9372111360, JSP-000198 small-k submission.
Original module: EmptyPentagon/SmallHoles.lean
Source/permission records: EmptyPentagon/UPSTREAM.md and LICENSE.
Local target: Lean 4.33.1 / pinned Mathlib 0df444a36.
-/
import Tengoku.Jsp000198Lean.EmptyPentagon.Forces
import Tengoku.Jsp000198Lean.EmptyPentagon.Parabola
import Tengoku.Jsp000198Lean.EmptyPentagon.Monotone
import Tengoku.Jsp000198Lean.EmptyPentagon.Triangle
import Tengoku.Jsp000198Lean.EmptyPentagon.FourWitness
import Tengoku.Jsp000198Lean.EmptyPentagon.Quadrilateral
import Tengoku.Jsp000198Lean.EmptyPentagon.NineWitness
import Tengoku.Jsp000198Lean.EmptyPentagon.Harborth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Horton.forces_empty_triangle_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Horton.forces_empty_quadrilateral_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Horton.forces_empty_pentagon_iff` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace Horton

/-- `h(3) = 3`: three points force an empty triangle, and no smaller number does.-/
theorem forces_empty_triangle_iff (n : ℕ) : ForcesEmptyKGon 3 n ↔ 3 ≤ n :=
  ⟨fun h ↦ h.le, fun h ↦ forcesEmptyKGon_of_le forcesEmptyKGon_three_three h⟩

/-- `h(4) = 5`: five points force an empty convex quadrilateral, and no smaller number does.-/
theorem forces_empty_quadrilateral_iff (n : ℕ) : ForcesEmptyKGon 4 n ↔ 5 ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ forcesEmptyKGon_of_le forcesEmptyKGon_four_five h⟩
  by_contra hn
  exact not_forcesEmptyKGon_of_le not_forcesEmptyKGon_four_four (by omega) h

/-- `h(5) = 10` (Harborth 1978): ten points force an empty convex pentagon, and no smaller
number does.-/
theorem forces_empty_pentagon_iff (n : ℕ) : ForcesEmptyKGon 5 n ↔ 10 ≤ n := by
  constructor
  · intro h
    by_contra hlt
    exact not_forcesEmptyKGon_of_le not_forcesEmptyKGon_five_nine (by omega) h
  · intro h
    exact forcesEmptyKGon_of_le forcesEmptyKGon_five_ten h

end Horton

