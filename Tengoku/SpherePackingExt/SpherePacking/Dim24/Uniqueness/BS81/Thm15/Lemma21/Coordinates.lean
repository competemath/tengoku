module
public import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinates in a `D₂₄` frame

In BS81 Lemma 21 we work in `ℝ²⁴` with an orthonormal frame `e : Fin 24 → ℝ²⁴` coming from the
embedding `D₂₄ ⊆ latticeL C` (Lemma 20). This file defines the coordinate function `coord` and
records the basic expansions in an orthonormal basis (coordinate formula and Parseval).

## Main definitions
* `coord`

## Main statements
* `coord_eq_of_orthonormal`
* `norm_sq_eq_sum_coord_sq`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21

noncomputable section

open scoped RealInnerProductSpace Pointwise

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- Coordinates of a vector in an orthonormal frame `e : Fin 24 → ℝ²⁴`.-/
@[expose] public def coord (e : Fin 24 → ℝ²⁴) (i : Fin 24) (x : ℝ²⁴) : ℝ :=
  ⟪e i, x⟫

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21
