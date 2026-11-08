module
public import Tengoku.Seed.Analysis.SpecialFunctions.SmoothTransition
public import Tengoku.Seed.Analysis.InnerProductSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth cutoff for radial Schwartz constructions

`cutoff : ℝ → ℝ` is a smooth function with
* `cutoff r = 0` for `r ≤ -1`;
* `cutoff r = 1` for `0 ≤ r`.

We use it to upgrade one-sided (i.e. `r ≥ 0`) decay bounds for radial profiles `f : ℝ → ℂ` into
global Schwartz bounds for `r ↦ cutoff r * f r`, without changing the induced function on
`F` via `r = ‖x‖^2`.
-/

namespace RadialSchwartz

noncomputable section

open Complex Real

-- We choose a transition region contained in `[-1/2, 0]`. This ensures the cutoff is identically
-- zero on a neighborhood of `(-1 : ℝ)`, which is convenient for profiles that are only naturally
-- smooth for `r > -1`.
/-- A smooth cutoff function on `ℝ` with `cutoff r = 0` for `r ≤ -1/2` and `cutoff r = 1` for
`0 ≤ r`.-/
@[expose] public def cutoff (r : ℝ) : ℝ := Real.smoothTransition (2 * r + 1)

/-- `cutoff r = 0` for `r ≤ -1/2`.-/
@[simp] public lemma cutoff_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoff r = 0 := by
  simpa [cutoff] using Real.smoothTransition.zero_of_nonpos (x := 2 * r + 1) (by linarith)

/-- `cutoff r = 0` for `r ≤ -1`.-/
@[simp] public lemma cutoff_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoff r = 0 :=
  cutoff_eq_zero_of_le_neg_half (r := r) (by linarith [hr])

/-- `cutoff r = 1` for `0 ≤ r`.-/
@[simp] public lemma cutoff_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoff r = 1 := by
  simpa [cutoff] using Real.smoothTransition.one_of_one_le (x := 2 * r + 1) (by linarith)

/-- Complex-valued version of `cutoff`.-/
@[expose] public def cutoffC (r : ℝ) : ℂ := (cutoff r : ℂ)

/-- `cutoffC r = 0` for `r ≤ -1/2`.-/
@[simp] public lemma cutoffC_eq_zero_of_le_neg_half {r : ℝ} (hr : r ≤ (-1 / 2 : ℝ)) :
    cutoffC r = 0 := by
  simp [cutoffC, cutoff_eq_zero_of_le_neg_half hr]

/-- `cutoffC r = 0` for `r ≤ -1`.-/
@[simp] public lemma cutoffC_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : cutoffC r = 0 := by
  simp [cutoffC, cutoff_eq_zero_of_le hr]

/-- `cutoffC r = 1` for `0 ≤ r`.-/
@[simp] public lemma cutoffC_eq_one_of_nonneg {r : ℝ} (hr : 0 ≤ r) : cutoffC r = 1 := by
  simp [cutoffC, cutoff_eq_one_of_nonneg hr]

/-- `cutoff (‖x‖^2) = 1` for all `x`.-/
@[simp] public lemma cutoff_norm_sq_eq_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) : cutoff (‖x‖ ^ 2) = 1 :=
  cutoff_eq_one_of_nonneg (r := ‖x‖ ^ 2) (sq_nonneg ‖x‖)

/-- `cutoffC (‖x‖^2) = 1` for all `x`.-/
@[simp] public lemma cutoffC_norm_sq_eq_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) : cutoffC (‖x‖ ^ 2) = 1 := by
  simp [cutoffC]

end

end RadialSchwartz
