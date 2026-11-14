import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The parameter triple used throughout the paper and its elementary
arithmetic certificates.
-/

namespace PiIrrationality
def a : ℚ := 1857
def b : ℚ := 3714
def c : ℚ := 5570

def alphaStar : ℚ := a / c
def betaStar : ℚ := b / c

def d0 : ℚ := 2 * a + 4 * b - 2 * c
def h : ℚ := 5 * b - 5 * c / 2

noncomputable def bound : ℝ := (7101862832357 : ℝ) / 10^12

theorem alphaStar_eq : alphaStar = 1857 / 5570 := by
  norm_num [alphaStar, a, c]

theorem betaStar_eq : betaStar = 1857 / 2785 := by
  norm_num [betaStar, b, c]

theorem d0_eq : d0 = 7430 := by
  norm_num [d0, a, b, c]

theorem h_eq : h = 4645 := by
  norm_num [h, b, c]

theorem chamber_alpha_beta : alphaStar + betaStar > 1 := by
  norm_num [alphaStar, betaStar, a, b, c]

theorem chamber_two_beta : 2 * betaStar > 1 := by
  norm_num [betaStar, b, c]

theorem chamber_seven_beta : 7 * betaStar < 5 := by
  norm_num [betaStar, b, c]

theorem chamber_last : 2 * alphaStar + 4 * betaStar - 2 > 1 := by
  norm_num [alphaStar, betaStar, a, b, c]

theorem bound_lt_seven_point_two : bound < (72 : ℝ) / 10 := by
  norm_num [bound]

end PiIrrationality
