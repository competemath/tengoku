/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Tengoku.Sendov.Sendov.FiniteRange.Reduce

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite-range claim in degree eight

The first degree proved entirely through the general machinery of
`Sendov.FiniteRange.Reduce`, with no hand computation of the integral: `Sendov.integral_eq_mom`
turns the integral into `Sendov.mom 8 α 2`, `Sendov.mom_two` evaluates it, and
`Sendov.alpha_le_half_M` supplies `α ≤ 7/2`.  Degrees five, six and seven predate that
machinery and still compute their integrals by hand; this file is the template for the
remaining degrees.

With `M 8 = 7`, `A 8 α = 1 - 2α/7` and `c 8 α = (42 + α - 2α²)/(14(3+α))`, the bound is
`1 - P α / (72030 (3+α)³)` with

  `P α = -240α⁶ - 7488α⁵ - 60624α⁴ + 747712α³ - 700161α² + 882882α + 1102059`,

positive up to `α = 5.852`, where only `α ≤ 7/2` is needed.
-/

namespace Sendov

open MeasureTheory

variable {α : ℝ}

/--
@isnad1 id=eq.0h0v.s4.06d6cb032799 from=translated src=- shape=1ac31801 vocab=01968c3c
-/
lemma M_eight : M 8 = 7 := by norm_num [M]

/--
@isnad1 id=eq.0h1v.s5.0bcd6e80dd41 from=translated src=- shape=f051650d vocab=57fb25bd
-/
lemma A_eight (α : ℝ) : A 8 α = 1 - 2 * α / 7 := by
  rw [A, M]
  push_cast
  ring

/--
@isnad1 id=eq.0h1v.s6.4b069aabc7f0 from=translated src=- shape=56895de3 vocab=fc8b4408
-/
lemma c_eight (α : ℝ) : c 8 α = 1 - α / 7 - α / (2 * (3 + α)) := by
  rw [c, M]
  push_cast
  ring

/--
@isnad1 id=eq.1h1v.s6.50ea24fa4ead from=translated src=- shape=2a8ab6b9 vocab=a488b366
-/
lemma c_eight' (hα : 0 ≤ α) : c 8 α = (42 + α - 2 * α ^ 2) / (14 * (3 + α)) := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  rw [c_eight]
  field_simp
  ring

/-- The upper bound for `R 8 α`, obtained from the general moment formula.
@isnad1 id=le.1h1v.s8.44d1b13a544c from=translated src=- shape=707f376a vocab=bc71373d
-/
lemma R_eight_le (hα : 0 ≤ α) :
    R 8 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2 := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  have hk : ((((8 : ℕ) : ℝ) - 4) / 2) = ((2 : ℕ) : ℝ) := by norm_num
  have h := R_le_of_integral_le (n := 8) (by norm_num) hα (le_of_eq (integral_eq_mom 2 hk))
  rw [M_eight] at h
  push_cast at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The finite-range claim in degree eight.**
@isnad1 id=lt.2h1v.s6.5a8c012affb0 from=translated src=- shape=76f861f6 vocab=6ae490cc
-/
theorem finite_range_eight (hα : 0 ≤ α) (hfeas : c 8 α ^ 2 ≤ A 8 α) : R 8 α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hle : α ≤ 7 / 2 := by
    have h := alpha_le_half_M (n := 8) (by norm_num) hfeas
    rw [M_eight] at h
    linarith
  have hR := R_eight_le hα
  have hid : 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2
      = 1 - (-240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
          + 882882 * α + 1102059) / (72030 * (3 + α) ^ 3) := by
    rw [mom_two, A_eight, c_eight' hα]
    field_simp
    ring
  rw [hid] at hR
  have hP : 0 < -240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
      + 882882 * α + 1102059 := by
    nlinarith [mul_nonneg (pow_nonneg hα 5) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 4) (sub_nonneg.2 hle),
      mul_nonneg (pow_nonneg hα 3) (sub_nonneg.2 hle),
      mul_nonneg hα (sq_nonneg (867020 * α - 700161)), hα, sq_nonneg α]
  have : 0 < (-240 * α ^ 6 - 7488 * α ^ 5 - 60624 * α ^ 4 + 747712 * α ^ 3 - 700161 * α ^ 2
      + 882882 * α + 1102059) / (72030 * (3 + α) ^ 3) := div_pos hP (by positivity)
  linarith

end Sendov
