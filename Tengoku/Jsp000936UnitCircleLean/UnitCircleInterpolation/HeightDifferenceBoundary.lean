/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapWidths
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.GapHeightComparison
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.FiniteHeightDifferences
import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PeakHeightDerivative
import Tengoku.Seed.Order.Filter.AtTopBot.Tendsto

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative boundary bounds for the actual height-difference map

An actual gap has at least the average width. Comparing its height with that
of a smallest gap, then bounding their difference by the actual adjacent-height
vector, yields an explicit reciprocal-width estimate. A bounded vector keeps
every gap uniformly positive. These statements prove the boundary estimates;
global properness of the height-difference map is a separate assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The fixed coefficient supplied by the mean width of the `d+1` actual gaps.-/
def heightDifferenceBoundaryCoefficient (d : ℕ) : ℝ :=
  2 * Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) ^ d

/--
@isnad1 id=lt.0h1v.s3.82e45ec88c83 from=translated src=- shape=b9369acb vocab=90fb5ded
-/
lemma heightDifferenceBoundaryCoefficient_pos (d : ℕ) :
    0 < heightDifferenceBoundaryCoefficient d := by
  have hn : 0 < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  have hn1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_one] using
      (show ((1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) from Nat.cast_le.mpr (by omega))
  have havg : 0 < 2 * Real.pi / ((d + 1 : ℕ) : ℝ) :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hn
  have havg_le : 2 * Real.pi / ((d + 1 : ℕ) : ℝ) ≤ 2 * Real.pi := by
    apply (div_le_iff₀ hn).mpr
    have h := mul_le_mul_of_nonneg_left hn1 (by positivity : 0 ≤ 2 * Real.pi)
    simpa only [mul_one] using h
  have hsin : 0 < Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) := by
    simpa only [sub_zero] using
      sin_quarter_gap_pos 0 (2 * Real.pi / ((d + 1 : ℕ) : ℝ)) havg
        (by simpa only [sub_zero] using havg_le)
  exact mul_pos (by norm_num) (pow_pos hsin _)

/--
@isnad1 id=eq.1h2v.s5.81e10f072883 from=translated src=- shape=d13c4c4d vocab=74ab6c2f
-/
lemma finiteHeightDifferences_parameterOrderedHeightMap (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) :
    finiteHeightDifferences (parameterOrderedHeightMap hsize u) =
      parameterAdjacentHeightDifferences hsize u := rfl

/-- The actual chart vector controls heights of any two actual raw circular gaps.
@isnad1 id=le.2h4v.s7.8f4c2e7fd780 from=translated src=- shape=97e93bce vocab=70279226
-/
lemma parameter_gapHeight_difference_le_two_dim_norm (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (large small : Fin (d + 1)) :
    gapHeight (cyclicAnglesOfParameters u hu) hsize large -
        gapHeight (cyclicAnglesOfParameters u hu) hsize small ≤
      2 * (d : ℝ) * ‖parameterAdjacentHeightDifferences hsize u‖ := by
  obtain ⟨i, hi⟩ := physicalGapCut_surjective (Nat.succ_pos d) large
  obtain ⟨j, hj⟩ := physicalGapCut_surjective (Nat.succ_pos d) small
  have h := height_sub_le_two_dim_mul_norm (parameterOrderedHeightMap hsize u) i j
  rw [finiteHeightDifferences_parameterOrderedHeightMap] at h
  change parameterOrderedHeight hsize i u - parameterOrderedHeight hsize j u ≤ _ at h
  simpa only [parameterOrderedHeight_of_mem_domain u hu, orderedHeight, hi, hj] using h

/-- The unconditional reciprocal estimate uses the actual minimum gap and actual difference norm.
@isnad1 id=le.2h2v.s7.f15088a7736f from=translated src=- shape=6c2d782f vocab=0548f49e
-/
theorem minimumGapWidth_reciprocal_le_adjacent_height_norm (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) :
    heightDifferenceBoundaryCoefficient d /
        minimumGapWidth (cyclicAnglesOfParameters u hu) - 1 ≤
      2 * (d : ℝ) * ‖parameterAdjacentHeightDifferences hsize u‖ := by
  let angles := cyclicAnglesOfParameters u hu
  have hmin : 0 < minimumGapWidth angles := minimumGapWidth_pos angles
  have hn : 0 < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  have havg : 0 < 2 * Real.pi / ((d + 1 : ℕ) : ℝ) :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hn
  have hcoeff : 2 * Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) ^ ((d + 1) - 1) =
      heightDifferenceBoundaryCoefficient d := by
    simp only [Nat.add_sub_cancel, heightDifferenceBoundaryCoefficient]
  by_cases hsmall : minimumGapWidth angles ≤ heightDifferenceBoundaryCoefficient d
  · obtain ⟨large, hlarge⟩ := exists_gapWidth_ge_average angles
    obtain ⟨small, heq⟩ := exists_gapWidth_eq_minimum angles
    have hgap : gapWidth angles small ≤
        2 * Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) ^ ((d + 1) - 1) := by
      rw [heq, hcoeff]
      exact hsmall
    have h := gapHeight_difference_lower_bound angles hsize large small
      (2 * Real.pi / ((d + 1 : ℕ) : ℝ)) havg hlarge hgap
    rw [hcoeff, heq] at h
    exact h.trans (parameter_gapHeight_difference_le_two_dim_norm hsize u hu large small)
  · have hdiv : heightDifferenceBoundaryCoefficient d / minimumGapWidth angles ≤ 1 :=
      (div_le_one hmin).mpr (le_of_lt (lt_of_not_ge hsmall))
    have hnorm : 0 ≤ 2 * (d : ℝ) * ‖parameterAdjacentHeightDifferences hsize u‖ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (norm_nonneg _)
    exact (sub_nonpos.mpr hdiv).trans hnorm

/--
@isnad1 id=lt.1h2v.s6.d93e7595b7eb from=translated src=- shape=e5bf2ed9 vocab=abe49d9a
-/
lemma heightDifferenceBoundaryMargin_pos (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R) := by
  exact div_pos (heightDifferenceBoundaryCoefficient_pos d) (by positivity)

/-- A bounded actual adjacent-height vector forces an explicit positive minimum width.
@isnad1 id=le.4h3v.s7.e36b5a520e61 from=translated src=- shape=66fce013 vocab=a7f5c742
-/
theorem minimumGapWidth_lower_of_adjacent_height_norm_le (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ‖parameterAdjacentHeightDifferences hsize u‖ ≤ R) :
    heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R) ≤
      minimumGapWidth (cyclicAnglesOfParameters u hu) := by
  have h := minimumGapWidth_reciprocal_le_adjacent_height_norm hsize u hu
  have hm := minimumGapWidth_pos (cyclicAnglesOfParameters u hu)
  have hscaled := mul_le_mul_of_nonneg_left hnorm
    (by positivity : 0 ≤ 2 * (d : ℝ))
  have hquot : heightDifferenceBoundaryCoefficient d /
      minimumGapWidth (cyclicAnglesOfParameters u hu) ≤ 1 + 2 * (d : ℝ) * R := by
    linarith
  have hmul := (div_le_iff₀ hm).mp hquot
  apply (div_le_iff₀ (by positivity : 0 < 1 + 2 * (d : ℝ) * R)).mpr
  simpa only [mul_comm] using hmul

/-- The same fixed positive lower width controls every literal gap in the ambient chart.
@isnad1 id=le.4h4v.s7.2f8c2e57c1fd from=translated src=- shape=2ec1a3a5 vocab=f77c1704
-/
theorem parameterGapWidth_lower_of_adjacent_height_norm_le (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ‖parameterAdjacentHeightDifferences hsize u‖ ≤ R) (cut : Fin (d + 1)) :
    heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R) ≤
      parameterGapWidth cut u := by
  rw [parameterGapWidth_of_mem_domain u hu]
  exact (minimumGapWidth_lower_of_adjacent_height_norm_le hsize u hu R hR hnorm).trans
    (minimumGapWidth_le (cyclicAnglesOfParameters u hu) cut)

/-- Crossing the explicit minimum-width threshold forces the actual norm above `R`.
@isnad1 id=lt.4h3v.s7.f61789223358 from=translated src=- shape=845e2243 vocab=4f7eca4b
-/
theorem lt_adjacent_height_norm_of_minimumGapWidth_lt (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (R : ℝ) (hR : 0 ≤ R)
    (hwidth : minimumGapWidth (cyclicAnglesOfParameters u hu) <
      heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R)) :
    R < ‖parameterAdjacentHeightDifferences hsize u‖ := by
  by_contra h
  have hnorm : ‖parameterAdjacentHeightDifferences hsize u‖ ≤ R := le_of_not_gt h
  exact (not_le_of_gt hwidth)
    (minimumGapWidth_lower_of_adjacent_height_norm_le hsize u hu R hR hnorm)

/-- Along any family in the actual chart, minimum width tending to zero forces norm divergence.
@isnad1 id=tendsto.3h4v.s7.83356a8151f2 from=translated src=- shape=14fa593a vocab=73298849
-/
theorem adjacent_height_norm_tendsto_atTop_of_minimumGapWidth_tendsto_zero
    {α : Type*} (hsize : 2 ≤ d + 1) (u : α → Fin d → ℝ)
    (hu : ∀ a, u a ∈ angularParameterDomain d) (l : Filter α)
    (hwidth : Filter.Tendsto (fun a => minimumGapWidth (cyclicAnglesOfParameters (u a) (hu a)))
      l (nhds (0 : ℝ))) :
    Filter.Tendsto (fun a => ‖parameterAdjacentHeightDifferences hsize (u a)‖)
      l Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro R
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hmargin := heightDifferenceBoundaryMargin_pos d (max R 0) hR
  have hevent := hwidth.eventually (gt_mem_nhds hmargin)
  filter_upwards [hevent] with a ha
  exact (le_max_left R 0).trans
    (lt_adjacent_height_norm_of_minimumGapWidth_lt hsize (u a) (hu a) (max R 0) hR ha).le

end

end UnitCircleInterpolation
