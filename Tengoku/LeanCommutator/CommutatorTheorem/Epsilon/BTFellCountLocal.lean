import Tengoku.LeanCommutator.CommutatorTheorem.Epsilon.BTFellSignLocal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local constancy of half-line root counts in a Fell pencil
-/

open scoped Polynomial Topology

namespace CommutatorTheorem.BTFellCountLocal

open Polynomial Set Filter
open CommutatorTheorem
open CommutatorTheorem.BTFellPair
open CommutatorTheorem.BTFellCrossGap
open CommutatorTheorem.BTFellExactDescartes
open CommutatorTheorem.BTFellCountParity
open CommutatorTheorem.BTFellSignLocal

private noncomputable def pencil (p q : ℝ[X]) (t : ℝ) : ℝ[X] :=
  t • p + (1 - t) • q

end CommutatorTheorem.BTFellCountLocal
