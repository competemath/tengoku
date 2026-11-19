/-
Elementary logarithm estimates for the fixed endpoint constants.
The rational decimal bounds used below are Mathlib theorems, not floating-point tests.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators Topology

noncomputable section
namespace Erdos647Sieve.Elementary

/-- A quadratic upper bound with the exact coefficient needed by the main term.-/
theorem neg_log_one_sub_le_add_sq (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ t + t ^ 2 := by
  let f : ℝ → ℝ := fun u => u + u ^ 2 + Real.log (1 - u)
  let g : ℝ → ℝ := fun u => u * (1 - 2 * u) / (1 - u)
  have hd : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), HasDerivAt f (g u) u := by
    intro u hu
    have hden : 1 - u ≠ 0 := by linarith [hu.2]
    have h := ((hasDerivAt_id u).add (hasDerivAt_pow 2 u)).add
      (((hasDerivAt_id u).const_sub 1).log hden)
    apply h.congr_deriv
    dsimp [g]
    field_simp [hden]
    ring
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd u (interior_subset hu)).hasDerivWithinAt) ?_
    intro u hu
    have huu := interior_subset hu
    have hu0 : 0 ≤ u := huu.1
    have hu1 : u ≤ (1 / 2 : ℝ) := huu.2
    dsimp [g]
    apply div_nonneg
    · exact mul_nonneg hu0 (by linarith)
    · linarith
  have h := hmono (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 2)) ⟨ht0, ht⟩ ht0
  dsimp [f] at h
  norm_num at h
  linarith

/-- The fixed positive gap; a lower bound using log 8 already suffices.-/
theorem endpoint_log_gap :
    (3 / 2 : ℝ) < Real.log (25 / 2) + 1 / Real.log 2 - 2 := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : (693 / 1000 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hupp : Real.log 2 < (7 / 10 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  have hinv : (10 / 7 : ℝ) ≤ 1 / Real.log 2 := by
    apply (le_div_iff₀ hlog0).mpr
    nlinarith
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) (3 : ℕ)
    norm_num at h
    exact h
  have hmono : Real.log (8 : ℝ) ≤ Real.log (25 / 2) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [h8] at hmono
  linarith

/-- The numerical coefficient in the factorial-tail exponent.-/
theorem endpoint_tail_log_constant :
    (1 / 30 : ℝ) ≤ (Real.log 20 - 1) / 50 - 1 / 500 := by
  have hlow : (693 / 1000 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) (4 : ℕ)
    norm_num at h
    exact h
  have hmono : Real.log (16 : ℝ) ≤ Real.log 20 :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [h16] at hmono
  linarith

end Erdos647Sieve.Elementary
end
