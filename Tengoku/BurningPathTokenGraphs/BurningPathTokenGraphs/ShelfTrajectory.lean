import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.Potential
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Accumulated estimates for shelf trajectories

This file formalizes equation (23).  The recurrence-specific module only has
to verify the listed one-step hypotheses.
-/

open scoped BigOperators

namespace BurningPath

private theorem sum_range_forward_difference (z : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (z i - z (i + 1)) = z 0 - z m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/--
The square-sum estimate in (23), under the required monotonicity and
decrement hypotheses.
@isnad1 id=le.5h3v.s8.4b8d86145485 from=translated src=- shape=a94de572 vocab=c3b6af6b
-/
theorem shelfTrajectory_sum_sq_le {m : ℕ} (w z : ℕ → ℝ)
    (hwNonneg : ∀ i ≤ m, 0 ≤ w i)
    (hzFinal : 0 ≤ z m)
    (hwBound : ∀ i < m, w i ≤ w 0)
    (hwNext : ∀ i < m, 3 * w i ≤ 4 * w (i + 1))
    (hzStep : ∀ i < m, z i - z (i + 1) = 2 * w (i + 1)) :
    ∑ i ∈ Finset.range m, w i ^ 2 ≤ (2 / 3 : ℝ) * w 0 * z 0 := by
  have hw0 : 0 ≤ w 0 := hwNonneg 0 (Nat.zero_le m)
  have hpoint :
      ∀ i ∈ Finset.range m,
        w i ^ 2 ≤ (4 / 3 : ℝ) * w 0 * w (i + 1) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hwi : 0 ≤ w i := hwNonneg i (Nat.le_of_lt him)
    have hmul : w i * w i ≤ w 0 * w i :=
      mul_le_mul_of_nonneg_right (hwBound i him) hwi
    have hnext := hwNext i him
    have hscale :
        3 * (w 0 * w i) ≤ 4 * (w 0 * w (i + 1)) := by
      nlinarith
    nlinarith [hmul]
  have hsumNext :
      ∑ i ∈ Finset.range m, w (i + 1) = (z 0 - z m) / 2 := by
    have htel := sum_range_forward_difference z m
    have hsteps :
        ∑ i ∈ Finset.range m, (z i - z (i + 1)) =
          ∑ i ∈ Finset.range m, 2 * w (i + 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hzStep i (Finset.mem_range.mp hi)
    rw [hsteps] at htel
    rw [← Finset.mul_sum] at htel
    nlinarith
  calc
    ∑ i ∈ Finset.range m, w i ^ 2 ≤
        ∑ i ∈ Finset.range m, (4 / 3 : ℝ) * w 0 * w (i + 1) :=
      Finset.sum_le_sum hpoint
    _ = (4 / 3 : ℝ) * w 0 * (∑ i ∈ Finset.range m, w (i + 1)) := by
      rw [Finset.mul_sum]
    _ = (2 / 3 : ℝ) * w 0 * (z 0 - z m) := by
      rw [hsumNext]
      ring
    _ ≤ (2 / 3 : ℝ) * w 0 * z 0 := by
      nlinarith

/-- Summing one-step potential losses gives the exact accumulated loss.
@isnad1 id=le.1h3v.s7.a023c81c50cd from=translated src=- shape=5c29284d vocab=f7466023
-/
theorem shelfPotential_trajectory_loss {m : ℕ} (w z : ℕ → ℝ)
    (hstep :
      ∀ i < m,
        shelfPotential (w (i + 1)) (z (i + 1)) ≥
          shelfPotential (w i) (z i) - 45 * w i ^ 2) :
    shelfPotential (w m) (z m) ≥
      shelfPotential (w 0) (z 0) -
        45 * (∑ i ∈ Finset.range m, w i ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hprefix :
          shelfPotential (w m) (z m) ≥
            shelfPotential (w 0) (z 0) -
              45 * (∑ i ∈ Finset.range m, w i ^ 2) := by
        apply ih
        intro i hi
        exact hstep i (hi.trans (Nat.lt_succ_self m))
      have hlast := hstep m (Nat.lt_succ_self m)
      rw [Finset.sum_range_succ]
      nlinarith

/-- Equation (23): the square-sum estimate converts `45` per step into total loss `30 w₀z₀`.
@isnad1 id=le.2h3v.s7.80cd442bde9f from=translated src=- shape=161af167 vocab=397f2b0e
-/
theorem shelfPotential_trajectory_lower {m : ℕ} (w z : ℕ → ℝ)
    (hsum :
      ∑ i ∈ Finset.range m, w i ^ 2 ≤ (2 / 3 : ℝ) * w 0 * z 0)
    (hstep :
      ∀ i < m,
        shelfPotential (w (i + 1)) (z (i + 1)) ≥
          shelfPotential (w i) (z i) - 45 * w i ^ 2) :
    shelfPotential (w m) (z m) ≥
      shelfPotential (w 0) (z 0) - 30 * w 0 * z 0 := by
  have hloss := shelfPotential_trajectory_loss w z hstep
  nlinarith

end BurningPath
