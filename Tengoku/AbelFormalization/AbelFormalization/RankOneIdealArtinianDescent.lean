import Tengoku.AbelFormalization.AbelFormalization.RankOneIdealInitialHilbert
import Tengoku.AbelFormalization.AbelFormalization.RankOneIdealWindowRecurrence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Artinian stabilization of the rank-one initial-ideal iteration

This file closes the abstract finite-descent argument for the rank-one ideal
sequence

`I₀ = in(Q)`, `I_(j+1) = in(J(I_j))`.

The Artinian uniform generator theorem supplies one ordinary-degree window
for every `I_j` and every intermediate ideal `J(I_j)`.  Equality of the
ordinary Hilbert lengths along the sequence follows from two facts: `J`
preserves the lengths of ordinary slices, and full lexicographic initial
formation preserves them.  The bounded-window recurrence then invokes
`exists_lexicographicInitialIdealIteration_stabilizes_of_window_data`.

The hypotheses concerning `Jmodule` are the exact interface expected from a
concrete polynomial automorphism: it realizes the action of `J` on rank-one
bounded parts, preserves every ordinary window, and is strictly lower
triangular in the ordered lexicographic weights.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Hilbert lengths along the recursive ideal sequence -/

/-! ## Artinian descent -/

end AbelFormalization
