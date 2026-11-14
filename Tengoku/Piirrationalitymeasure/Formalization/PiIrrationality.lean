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

/--
@isnad1 id=eq.0h0v.s4.03f29ebbefec from=translated src=- shape=0efb1284 vocab=e737bd8c
-/
theorem alphaStar_eq : alphaStar = 1857 / 5570 := by
  norm_num [alphaStar, a, c]

/--
@isnad1 id=eq.0h0v.s4.4388f6ee48e2 from=translated src=- shape=0efb1284 vocab=d76f2179
-/
theorem betaStar_eq : betaStar = 1857 / 2785 := by
  norm_num [betaStar, b, c]

/--
@isnad1 id=eq.0h0v.s3.7135ec4c6734 from=translated src=- shape=ffdda526 vocab=babde22d
-/
theorem d0_eq : d0 = 7430 := by
  norm_num [d0, a, b, c]

/--
@isnad1 id=eq.0h0v.s3.a95e8aa486be from=translated src=- shape=ffdda526 vocab=9a4987d3
-/
theorem h_eq : h = 4645 := by
  norm_num [h, b, c]

/--
@isnad1 id=lt.0h0v.s4.61f172175041 from=translated src=- shape=33aceabd vocab=c7e17dd9
-/
theorem chamber_alpha_beta : alphaStar + betaStar > 1 := by
  norm_num [alphaStar, betaStar, a, b, c]

/--
@isnad1 id=lt.0h0v.s4.3e64a5f32a8b from=translated src=- shape=f1614c97 vocab=2fc5574b
-/
theorem chamber_two_beta : 2 * betaStar > 1 := by
  norm_num [betaStar, b, c]

/--
@isnad1 id=lt.0h0v.s4.d3f9f4595d2a from=translated src=- shape=f1614c97 vocab=10debbd5
-/
theorem chamber_seven_beta : 7 * betaStar < 5 := by
  norm_num [betaStar, b, c]

/--
@isnad1 id=lt.0h0v.s5.8fbf73fbe4ba from=translated src=- shape=d7077f17 vocab=64a3a701
-/
theorem chamber_last : 2 * alphaStar + 4 * betaStar - 2 > 1 := by
  norm_num [alphaStar, betaStar, a, b, c]

/--
@isnad1 id=lt.0h0v.s4.5926bf436cc8 from=translated src=- shape=0efb1284 vocab=1bf111c7
-/
theorem bound_lt_seven_point_two : bound < (72 : ℝ) / 10 := by
  norm_num [bound]

end PiIrrationality
