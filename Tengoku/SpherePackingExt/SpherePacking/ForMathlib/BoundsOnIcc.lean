module

public import Tengoku.Seed.Topology.Instances.Real.Lemmas
public import Tengoku.Seed.Order.Interval.Set.UnorderedInterval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounds on compact intervals

This file provides simple existence lemmas for upper and lower bounds of continuous real
functions on compact intervals in `ℝ`.

## Main statements
* `SpherePacking.ForMathlib.exists_upper_bound_on_Icc`
* `SpherePacking.ForMathlib.exists_upper_bound_on_uIoc`
* `SpherePacking.ForMathlib.exists_lower_bound_pos_on_Icc`
-/

namespace SpherePacking.ForMathlib

open Set
open scoped Interval

/-- A continuous function on `Icc a b` admits a (global) upper bound on that interval.-/
public lemma exists_upper_bound_on_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, g x ≤ C := by
  rcases (isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hg) with ⟨x0, -, hxmax⟩
  exact ⟨g x0, fun _ hx => hxmax hx⟩

/-- Variant of `exists_upper_bound_on_Icc` for a globally continuous function.-/
public lemma Continuous.exists_upper_bound_on_Icc {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hab : a ≤ b) : ∃ C, ∀ x ∈ Icc a b, g x ≤ C :=
  SpherePacking.ForMathlib.exists_upper_bound_on_Icc (g := g) hab hg.continuousOn

end SpherePacking.ForMathlib
