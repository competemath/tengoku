module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LatticeLIntegral
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.LatticeLShell4
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import Tengoku.Seed.Analysis.InnerProductSpace.Basic
import Tengoku.Seed.Tactic.ByContra
import Tengoku.Seed.Tactic.IntervalCases
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Half-integrality and value restrictions for BS81 Lemma 16

Let `L = span_ℤ (2 • C)` and suppose `v ∈ L` has `‖v‖ ^ 2 = 2`.
For any `u ∈ C`:
* `⟪2u, v⟫ ∈ ℤ` by integrality of `L`,
* hence `⟪u, v⟫ ∈ (1/2)ℤ`,
* and Cauchy-Schwarz forces `⟪u, v⟫ ∈ {0, ±1/2, ±1}`.

## Main statements
* `inner_twoU_v_halfInteger`
* `inner_mem_values_of_norm_sq_two`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace Pointwise

open Set

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
