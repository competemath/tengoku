/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PhaseBridge
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Concrete bounds for the literal unit-circle chords

The midpoint of any gap of length at most one full turn stays uniformly separated
from all canonical nodes outside that gap. The estimate includes gaps longer than
a half turn. These are geometric estimates only; no boundary coercivity theorem
is assumed or asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

/-- Sine is bounded below by its endpoint value throughout a symmetric interval.
@isnad1 id=le.3h2v.s5.967b09ebf567 from=translated src=- shape=97241dc7 vocab=092b4ea1
-/
lemma sin_sym_interval_lower_bound (r x : ℝ) (hr : 0 ≤ r)
    (hlo : r ≤ x) (hhi : x ≤ Real.pi - r) :
    Real.sin r ≤ Real.sin x := by
  by_cases hx : x ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hx hlo
  · rw [← Real.sin_pi_sub x]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) (by linarith) (by linarith)

/-- A positive gap of length at most one turn has a positive quarter-angle sine.
@isnad1 id=lt.2h2v.s6.7aed66635455 from=translated src=- shape=10470ede vocab=1b56ecb0
-/
lemma sin_quarter_gap_pos (a b : ℝ) (hab : a < b) (hwidth : b - a ≤ 2 * Real.pi) :
    0 < Real.sin ((b - a) / 4) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith [Real.pi_pos]

/-- The lower chord estimate uses the absolute half-angle over its entire canonical range.
@isnad1 id=le.3h3v.s8.98e6b5f2e409 from=translated src=- shape=897666c6 vocab=652dfec8
-/
lemma norm_phase_sub_lower_of_half_angle (r t s : ℝ) (hr : 0 ≤ r)
    (hlo : r ≤ |(t - s) / 2|) (hhi : |(t - s) / 2| ≤ Real.pi - r) :
    2 * Real.sin r ≤ ‖(Circle.exp t : ℂ) - (Circle.exp s : ℂ)‖ := by
  rw [norm_phase_sub, Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
  exact mul_le_mul_of_nonneg_left (sin_sym_interval_lower_bound r _ hr hlo hhi)
    (by norm_num)

/-- A gap midpoint is separated from every canonical angle outside that gap.
@isnad1 id=le.6h3v.s8.4605db84a482 from=translated src=- shape=986c1c2c vocab=5bb2acc2
-/
lemma norm_phase_midpoint_sub_lower_bound (a b v : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * Real.pi)
    (hv0 : 0 ≤ v) (hvT : v ≤ 2 * Real.pi) (hout : v ≤ a ∨ b ≤ v) :
    2 * Real.sin ((b - a) / 4) ≤
      ‖(Circle.exp ((a + b) / 2) : ℂ) - (Circle.exp v : ℂ)‖ := by
  apply norm_phase_sub_lower_of_half_angle
  · linarith
  · rcases hout with hva | hbv
    · rw [abs_of_nonneg (by linarith : 0 ≤ ((a + b) / 2 - v) / 2)]
      linarith
    · rw [abs_of_nonpos (by linarith : ((a + b) / 2 - v) / 2 ≤ 0)]
      linarith
  · rcases hout with hva | hbv
    · rw [abs_of_nonneg (by linarith : 0 ≤ ((a + b) / 2 - v) / 2)]
      linarith
    · rw [abs_of_nonpos (by linarith : ((a + b) / 2 - v) / 2 ≤ 0)]
      linarith

/-- The midpoint lower bound is strictly positive, including gaps approaching a full turn.
@isnad1 id=and.6h3v.s8.e5fffb1312dd from=translated src=- shape=17310bed vocab=5bb2acc2
-/
lemma norm_phase_midpoint_sub_lower_bound_pos (a b v : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * Real.pi)
    (hv0 : 0 ≤ v) (hvT : v ≤ 2 * Real.pi) (hout : v ≤ a ∨ b ≤ v) :
    0 < 2 * Real.sin ((b - a) / 4) ∧
      2 * Real.sin ((b - a) / 4) ≤
        ‖(Circle.exp ((a + b) / 2) : ℂ) - (Circle.exp v : ℂ)‖ := by
  refine ⟨mul_pos (by norm_num) (sin_quarter_gap_pos a b hab (by linarith)), ?_⟩
  exact norm_phase_midpoint_sub_lower_bound a b v ha hab hb hv0 hvT hout

/--
@isnad1 id=lt.6h3v.s8.bc390cfd4d58 from=translated src=- shape=c132b22f vocab=f2dfb098
-/
lemma norm_phase_midpoint_sub_pos (a b v : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * Real.pi)
    (hv0 : 0 ≤ v) (hvT : v ≤ 2 * Real.pi) (hout : v ≤ a ∨ b ≤ v) :
    0 < ‖(Circle.exp ((a + b) / 2) : ℂ) - (Circle.exp v : ℂ)‖ := by
  exact lt_of_lt_of_le
    (norm_phase_midpoint_sub_lower_bound_pos a b v ha hab hb hv0 hvT hout).1
    (norm_phase_midpoint_sub_lower_bound a b v ha hab hb hv0 hvT hout)

/-- A lower gap width gives a uniform quarter-angle sine lower bound.
@isnad1 id=le.3h3v.s6.aa101d376ccf from=translated src=- shape=48f74705 vocab=cecc5029
-/
lemma sin_quarter_le_of_gap_width (d a b : ℝ) (hd : 0 ≤ d)
    (hlo : d ≤ b - a) (hhi : b - a ≤ 2 * Real.pi) :
    Real.sin (d / 4) ≤ Real.sin ((b - a) / 4) := by
  exact Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith) (by linarith)

/-- The midpoint estimate is uniform over all gaps having a fixed positive lower width.
@isnad1 id=and.8h4v.s8.b5592125ec91 from=translated src=- shape=6a9af4ff vocab=5bb2acc2
-/
lemma norm_phase_midpoint_sub_uniform_lower_bound (d a b v : ℝ)
    (hd : 0 < d) (hwidth : d ≤ b - a)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * Real.pi)
    (hv0 : 0 ≤ v) (hvT : v ≤ 2 * Real.pi) (hout : v ≤ a ∨ b ≤ v) :
    0 < 2 * Real.sin (d / 4) ∧
      2 * Real.sin (d / 4) ≤
        ‖(Circle.exp ((a + b) / 2) : ℂ) - (Circle.exp v : ℂ)‖ := by
  refine ⟨mul_pos (by norm_num) ?_, ?_⟩
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  · exact (mul_le_mul_of_nonneg_left
      (sin_quarter_le_of_gap_width d a b hd.le hwidth (by linarith))
      (by norm_num)).trans
        (norm_phase_midpoint_sub_lower_bound a b v ha hab hb hv0 hvT hout)

/-- No node outside the gap is the actual complex midpoint phase.
@isnad1 id=ne.6h3v.s8.e83c775e6aca from=translated src=- shape=5260dd78 vocab=490f8914
-/
lemma phase_midpoint_ne_of_outside (a b v : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * Real.pi)
    (hv0 : 0 ≤ v) (hvT : v ≤ 2 * Real.pi) (hout : v ≤ a ∨ b ≤ v) :
    (Circle.exp ((a + b) / 2) : ℂ) ≠ (Circle.exp v : ℂ) := by
  intro heq
  have hpos := norm_phase_midpoint_sub_pos a b v ha hab hb hv0 hvT hout
  rw [heq, sub_self, norm_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The distance between arbitrary literal unit-circle points never exceeds the diameter.
@isnad1 id=le.0h2v.s7.a18df62545a6 from=translated src=- shape=cd7b6923 vocab=05037150
-/
lemma norm_circle_sub_le_two (z w : Circle) : ‖(z : ℂ) - (w : ℂ)‖ ≤ 2 := by
  calc
    ‖(z : ℂ) - (w : ℂ)‖ ≤ ‖(z : ℂ)‖ + ‖(w : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Circle.norm_coe, Circle.norm_coe]; norm_num

/-- The literal chord is bounded above by the unwrapped angular displacement.
@isnad1 id=le.0h2v.s7.25d7e9c620ae from=translated src=- shape=af20a93f vocab=f2f2ecf5
-/
lemma norm_phase_sub_le_abs_sub (t s : ℝ) :
    ‖(Circle.exp t : ℂ) - (Circle.exp s : ℂ)‖ ≤ |t - s| := by
  calc
    ‖(Circle.exp t : ℂ) - (Circle.exp s : ℂ)‖ =
        2 * |Real.sin ((t - s) / 2)| := norm_phase_sub t s
    _ ≤ 2 * |(t - s) / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs
      (by norm_num)
    _ = |t - s| := by rw [abs_div]; norm_num; ring

/-- For ordered angles the chord denominator is bounded by their literal positive gap.
@isnad1 id=le.1h2v.s7.18fe76b2e1d7 from=translated src=- shape=2a6ea538 vocab=f2797931
-/
lemma norm_phase_sub_le_sub (a b : ℝ) (hab : a ≤ b) :
    ‖(Circle.exp b : ℂ) - (Circle.exp a : ℂ)‖ ≤ b - a := by
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using norm_phase_sub_le_abs_sub b a

end

end UnitCircleInterpolation
