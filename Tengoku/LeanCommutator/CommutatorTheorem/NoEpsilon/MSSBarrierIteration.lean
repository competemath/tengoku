import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.MSSBarrierStep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite iteration of the quantitative MSS barrier step
-/

namespace NoEpsilon.MSSBarrierIteration

open NoEpsilon.MSSStability NoEpsilon.MSSBarrier NoEpsilon.MSSBarrierStep
open scoped BigOperators

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def advance (z : σ → ℝ) (δ : ℝ) (xs : List σ) : σ → ℝ :=
  xs.foldl (fun w i ↦ coordinateShift w i δ) z

omit [Fintype σ] in
/-- When a coordinate list has no repetitions, its successive shifts are exactly
one shift at each listed coordinate.-/
theorem advance_eq_of_nodup (z : σ → ℝ) (δ : ℝ) (xs : List σ) (hxs : xs.Nodup) :
    advance z δ xs = fun k ↦ z k + if k ∈ xs then δ else 0 := by
  induction xs generalizing z with
  | nil => simp [advance]
  | cons j xs ih =>
    have hj : j ∉ xs := (List.nodup_cons.mp hxs).1
    have hs : xs.Nodup := (List.nodup_cons.mp hxs).2
    change advance (coordinateShift z j δ) δ xs = _
    rw [ih _ hs]
    funext k
    by_cases hkj : k = j
    · subst k
      simp [coordinateShift, hj]
    · simp [coordinateShift, hkj]

omit [Fintype σ] in
/-- No coordinate moves by more than `δ` in a list with no repetitions.-/
theorem advance_le_uniform (t δ : ℝ) (hδ : 0 ≤ δ) (xs : List σ) (hxs : xs.Nodup) :
    advance (fun _ : σ ↦ t) δ xs ≤ fun _ ↦ t + δ := by
  rw [advance_eq_of_nodup _ _ _ hxs]
  intro k
  by_cases hk : k ∈ xs <;> simp [hk, hδ]

-- Preserve the existing parameter list for downstream callers.

end NoEpsilon.MSSBarrierIteration
