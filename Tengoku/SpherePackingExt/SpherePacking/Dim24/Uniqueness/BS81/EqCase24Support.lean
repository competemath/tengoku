module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Defs

import Tengoku.Seed.Data.Set.Card.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inner product support in the BS81 equality case

Fix `C : Set ℝ²⁴` satisfying `EqCase24 C`. The explicit distance distribution (equation (11) in
BS81) forces that, for each `u ∈ C`, every `v ∈ C` has inner product with `u` in the finite support
set `{1, -1, ±1/2, ±1/4, 0}`.

This file packages the fibers `distSet C u t` and proves the corresponding support lemma
`inner_eq_one_or_eq_neg_one_or_eq_half_or_eq_neg_half_or_eq_quarter_or_eq_neg_quarter_or_eq_zero`.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81

noncomputable section

open scoped BigOperators RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-- The fiber `{v ∈ C | ⟪u,v⟫ = t}`.-/
@[expose] public def distSet (C : Set ℝ²⁴) (u : ℝ²⁴) (t : ℝ) : Set ℝ²⁴ :=
  {v : ℝ²⁴ | v ∈ C ∧ (⟪u, v⟫ : ℝ) = t}

end

end SpherePacking.Dim24.Uniqueness.BS81
