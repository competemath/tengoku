import Tengoku.Jsp000937Lean.Erdos1153.Density.Asymptotic
import Tengoku.Jsp000937Lean.Erdos1153.Density.ConsecutiveBlock
import Tengoku.Jsp000937Lean.Erdos1153.Collapse.BlockAdapter
import Tengoku.Jsp000937Lean.Erdos1153.DeBoorPinkus.Package

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A finite witness from the dense alternative

The central indices of an ordered array form a literal consecutive block.
When the density alternative holds and its denominator is no larger than the
ambient cardinality, that block has at least two nodes.  The unconditional
de Boor--Pinkus package therefore supplies a normalized equioscillating
pattern of the matching cardinality, and the arbitrary-block collapse
adapter places its common height below the height of an actual gap of the
original array.

This file turns that gap-height conclusion into a pointwise witness in the
original interval.  The last step uses compact attainment on the *same*
original nodal gap and the checked containment of every central-block gap in
`[a,b]`.
-/

namespace Erdos1153.Density

open Set
open Erdos1153.Collapse
open Erdos1153.DeBoorPinkus

noncomputable section

/-- Under the dense alternative, once one density denominator fits in the
ambient cardinality, the central block contains at least two nodes.-/
lemma two_le_card_sparseIndices_of_dense {n K : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hden : densityDenominator K ≤ n)
    (hdense : DenseAt nodes.toNodeFamily a b K) :
    2 ≤ (sparseIndices nodes.toNodeFamily a b).card := by
  rw [denseAt_iff_div_lt_card] at hdense
  have hone : 1 ≤ n / densityDenominator K := by
    apply (Nat.le_div_iff_mul_le (densityDenominator_pos K)).2
    simpa only [one_mul] using hden
  omega

end

end Erdos1153.Density
