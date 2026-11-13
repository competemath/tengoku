import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellSignWordCrossing
import Tengoku.Seed.Data.Finset.DenselyOrdered

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Degree induction for Fell half-line root counts

Rolle sandwiches reduce the endpoint count comparison to normalized
derivatives.  A putative gap of two has even parity, hence equal endpoint
evaluation signs; local constancy then rules it out.
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTFellCountInduction

open Polynomial Set Filter
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellCrossGap
open CommutatorTheorem.BTFellRolleCount
open CommutatorTheorem.BTFellThreshold
open CommutatorTheorem.BTFellCountLocal

private noncomputable def pencil (p q : ℝ[X]) (t : ℝ) : ℝ[X] :=
  t • p + (1 - t) • q

/-- Degree-indexed form of the half-line count assertion, without a
root-disjointness hypothesis.-/
def PencilCountBalancedAtDegree (d : ℕ) : Prop :=
  ∀ (p q : ℝ[X]), p.Monic → q.Monic → RealRooted p → RealRooted q →
    p.natDegree = d → q.natDegree = d →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → RealRooted (pencil p q t)) →
    RootsGTCountBalanced p q

end CommutatorTheorem.BTFellCountInduction
