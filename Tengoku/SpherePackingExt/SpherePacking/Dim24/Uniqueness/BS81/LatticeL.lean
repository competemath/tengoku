module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Defs
public import Tengoku.Seed.Algebra.Module.Submodule.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The lattice `L` and its norm-`4` shell

We define the lattice `latticeL C := span_ℤ (2 • C)` associated to a code `C ⊆ ℝ²⁴`, together with
its norm-`4` shell `latticeShell4 C`. We also record lightweight helper lemmas used in the
Bannai-Sloane argument in BS81 Theorem 15.

## Main definitions
* `Uniqueness.BS81.latticeL`
* `Uniqueness.BS81.latticeShell4`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped RealInnerProductSpace Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The set `2 • C` as a subset of `ℝ²⁴`.-/
@[expose] public def twoCodeVectors (C : Set ℝ²⁴) : Set ℝ²⁴ :=
  (fun u : ℝ²⁴ => (2 : ℝ) • u) '' C

/-- BS81's lattice `L := span_ℤ (2 • C)`.-/
@[expose] public def latticeL (C : Set ℝ²⁴) : Submodule ℤ ℝ²⁴ :=
  Submodule.span ℤ (twoCodeVectors C)

/-- The norm-4 shell of `latticeL C`. (Recall `‖2u‖^2 = 4` for unit vectors `u`.)-/
@[expose] public def latticeShell4 (C : Set ℝ²⁴) : Set ℝ²⁴ :=
  {v : ℝ²⁴ | v ∈ (latticeL C : Set ℝ²⁴) ∧ ‖v‖ ^ 2 = (4 : ℝ)}

end

end SpherePacking.Dim24.Uniqueness.BS81
