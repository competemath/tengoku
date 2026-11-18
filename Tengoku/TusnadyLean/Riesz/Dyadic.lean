import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.Topology.MetricSpace.Lipschitz
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.SplitIfs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The one-dimensional profile used in the direct Riesz proof

`profile` is the primitive `w` from Section 2 of the manuscript.  It is extended by
zero outside the unit interval.  The lemmas in this file establish its actual
pointwise and integral properties; they are not hypotheses of a surrogate model.
-/

namespace Riesz

noncomputable section

/-- The continuous, mean-zero primitive of the four-quarter wavelet.-/
def profile (x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else if x ≤ 1 / 4 then x else
    if x ≤ 3 / 4 then 1 / 2 - x else if x ≤ 1 then x - 1 else 0

lemma profile_zero : profile 0 = 0 := by simp [profile]
lemma profile_one : profile 1 = 0 := by norm_num [profile]

lemma profile_of_nonpos {x : ℝ} (hx : x ≤ 0) : profile x = 0 := by
  simp [profile, hx]

lemma profile_of_one_le {x : ℝ} (hx : 1 ≤ x) : profile x = 0 := by
  unfold profile
  split_ifs <;> linarith

lemma abs_profile_le (x : ℝ) : |profile x| ≤ 1 / 4 := by
  unfold profile
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma profile_reflect (x : ℝ) : profile (1 - x) = -profile x := by
  unfold profile
  split_ifs <;> linarith

lemma abs_profile_sub_le (x y : ℝ) : |profile x - profile y| ≤ |x - y| := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    unfold profile
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    unfold profile
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma profile_lipschitz : LipschitzWith 1 profile := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa [Real.dist_eq] using abs_profile_sub_le x y

lemma profile_continuous : Continuous profile := profile_lipschitz.continuous

lemma integral_profile_zero : (∫ x in (0 : ℝ)..1, profile x) = 0 := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) profile 1
  simp only [sub_self, sub_zero, profile_reflect, intervalIntegral.integral_neg] at h
  linarith

lemma profile_first_quarter {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / 4)) :
    profile x = x := by
  unfold profile
  split_ifs <;> rcases hx with ⟨_, _⟩ <;> linarith

lemma profile_middle_half {x : ℝ} (hx : x ∈ Set.Icc (1 / 4) (3 / 4)) :
    profile x = 1 / 2 - x := by
  unfold profile
  split_ifs <;> rcases hx with ⟨_, _⟩ <;> linarith

lemma profile_last_quarter {x : ℝ} (hx : x ∈ Set.Icc (3 / 4) 1) :
    profile x = x - 1 := by
  unfold profile
  split_ifs <;> rcases hx with ⟨_, _⟩ <;> linarith

lemma integral_profile_left_half : (∫ x in (0 : ℝ)..(1 / 2), profile x) = 1 / 16 := by
  have hfirst : (∫ x in (0 : ℝ)..(1 / 4), profile x) = 1 / 32 := by
    calc (∫ x in (0 : ℝ)..(1 / 4), profile x) = ∫ x in (0 : ℝ)..(1 / 4), x := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply profile_first_quarter
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] using hx
      _ = 1 / 32 := by norm_num [integral_id]
  have hsecond : (∫ x in (1 / 4 : ℝ)..(1 / 2), profile x) = 1 / 32 := by
    calc (∫ x in (1 / 4 : ℝ)..(1 / 2), profile x) =
          ∫ x in (1 / 4 : ℝ)..(1 / 2), 1 / 2 - x := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply profile_middle_half
          simp only [Set.uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2), Set.mem_Icc] at hx
          exact ⟨hx.1, by linarith [hx.2]⟩
      _ = 1 / 32 := by
          rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 / 2 : ℝ))
            (g := fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
            (continuous_id.intervalIntegrable _ _)]
          norm_num [integral_id]
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (profile_continuous.intervalIntegrable (0 : ℝ) (1 / 4))
    (profile_continuous.intervalIntegrable (1 / 4 : ℝ) (1 / 2))
  linarith

lemma integral_profile_right_half : (∫ x in (1 / 2 : ℝ)..1, profile x) = -(1 / 16) := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (profile_continuous.intervalIntegrable (0 : ℝ) (1 / 2))
    (profile_continuous.intervalIntegrable (1 / 2 : ℝ) 1)
  rw [integral_profile_zero, integral_profile_left_half] at hsum
  linarith

end
end Riesz

namespace Riesz
noncomputable section
open Finset

/-- Values of the averaged profile in the four quarters, at a fixed local offset.-/
def quarterValue (q : Fin 4) (z : ℝ) : ℝ :=
  if q = 0 then z else if q = 1 then 1 / 4 - z else
    if q = 2 then -z else z - 1 / 4

/-- The average over the first two binary digits.-/
def quarterMean (z : ℝ) (f : ℝ → ℝ) : ℝ := (∑ q : Fin 4, f (quarterValue q z)) / 4

lemma quarterMean_id (z : ℝ) : quarterMean z id = 0 := by
  norm_num [quarterMean, Fin.sum_univ_succ, quarterValue]
  ring
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The midpoint of one of `m` equal cells in a quarter of the unit interval.-/
def quarterMidpoint (m : ℕ) (r : Fin m) : ℝ := ((r : ℕ) + 1 / 2) / (4 * m)

/-- Uniform expectation of the `4m` possible averaged profile values.  For depth
`L ≥ 2`, the manuscript uses `m = 2^(L-2)`.-/
def blockMean (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∑ r : Fin m, quarterMean (quarterMidpoint m r) f) / m

lemma blockMean_id (m : ℕ) : blockMean m id = 0 := by
  simp [blockMean, quarterMean_id]

end
end Riesz

namespace Riesz
noncomputable section

end
end Riesz
