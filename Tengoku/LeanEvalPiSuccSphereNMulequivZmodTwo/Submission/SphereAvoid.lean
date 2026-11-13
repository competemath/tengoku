import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SphereClose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Loops avoiding the antipode are nullhomotopic

A generalized loop in the unit sphere based at `x` whose image avoids the antipode
`-x` is homotopic rel boundary to the constant loop: it stays at distance `< 2` from
the constant loop at `x`, so the normalized-chord homotopy of
`Submission.SphereClose` applies.

Main declarations:

* `Submission.homotopic_const_of_avoids_antipode`;
* `Submission.homotopy_class_eq_const_of_avoids_antipode` (quotient version);
* `Submission.homotopy_class_eq_one_of_avoids_antipode` (group version).
-/

noncomputable section

open scoped Topology unitInterval
open Topology.Homotopy

namespace Submission

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Type*} {x : UnitSphere E}

/-- A generalized loop in the unit sphere avoiding the antipode of its basepoint is
homotopic rel boundary to the constant loop.
@isnad1 id=homotopi.1h4v.s9.629989659222 from=translated src=- shape=e3aeb557 vocab=5ac92373
-/
theorem homotopic_const_of_avoids_antipode (p : Ω^ N (UnitSphere E) x)
    (hp : ∀ t, p t ≠ -x) : GenLoop.Homotopic p GenLoop.const :=
  genLoop_homotopic_of_dist_lt_two p GenLoop.const fun t =>
    dist_lt_two_of_ne_neg (p t) x (hp t)

/-- Quotient version: the class of a generalized loop avoiding the antipode is the
class of the constant loop.
@isnad1 id=eq.1h4v.s10.fe9fdb7eb73f from=translated src=- shape=7a7a2b0f vocab=97dc16f9
-/
theorem homotopy_class_eq_const_of_avoids_antipode (p : Ω^ N (UnitSphere E) x)
    (hp : ∀ t, p t ≠ -x) :
    (⟦p⟧ : HomotopyGroup N (UnitSphere E) x) = ⟦GenLoop.const⟧ :=
  Quotient.sound (homotopic_const_of_avoids_antipode p hp)

/-- Group version: the class of a generalized loop avoiding the antipode is the
identity element of the homotopy group.
@isnad1 id=eq.1h4v.s10.9dd5c22f919f from=translated src=- shape=a20843ee vocab=d1923556
-/
theorem homotopy_class_eq_one_of_avoids_antipode [DecidableEq N] [Nonempty N]
    (p : Ω^ N (UnitSphere E) x) (hp : ∀ t, p t ≠ -x) :
    ⟦p⟧ = (1 : HomotopyGroup N (UnitSphere E) x) := by
  rw [HomotopyGroup.one_def]
  exact homotopy_class_eq_const_of_avoids_antipode p hp

end Submission
