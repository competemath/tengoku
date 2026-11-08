module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.BiplaneBasic
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parameters of the `2-(11,5,2)` biplane

This file formalizes the argument in the in-repo note
`paper/Notes/CodingTheory/golay_uniqueness_from_biplane.tex`, Lemma `biplane_from_intersections`.

Starting from a family of `11` blocks of size `5` on `11` points with constant pairwise
intersection size `2`, we prove:
- each point lies in exactly `5` blocks, and
- each pair of distinct points lies in exactly `2` blocks.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
noncomputable section

open scoped BigOperators

namespace Biplane.Structure

open Finset

variable (D : Structure)

/-!
## Constant point and pair counts
-/

end Biplane.Structure
end

end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
