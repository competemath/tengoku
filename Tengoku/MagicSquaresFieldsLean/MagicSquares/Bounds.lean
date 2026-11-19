import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-- The algebra behind `C₀(d) = (d-1)^2(2d+1)` in Section 12.
@isnad1 id=eq.0h1v.s7.2806e6fd7b50 from=translated src=- shape=c1ca0c55 vocab=fb2191f5
-/
theorem C0_closed_form (d : ℤ) :
    3 * (d - 1) ^ 2 + 2 * (d - 1) ^ 3 = (d - 1) ^ 2 * (2 * d + 1) := by
  ring

/-- Expanded verification of the binomial calculation in Section 14:
`C₁(d) = d^7(7d-8)+1`.

The coefficients are `choose 8 r * (r-1)` for `r = 2,...,8`.
@isnad1 id=eq.0h1v.s8.9184d29f1ba7 from=translated src=- shape=23892d13 vocab=fb2191f5
-/
theorem C1_closed_form (d : ℤ) :
    28 * (d - 1) ^ 2 +
    112 * (d - 1) ^ 3 +
    210 * (d - 1) ^ 4 +
    224 * (d - 1) ^ 5 +
    140 * (d - 1) ^ 6 +
    48 * (d - 1) ^ 7 +
    7 * (d - 1) ^ 8 =
      d ^ 7 * (7 * d - 8) + 1 := by
  ring

/-- The numerical inequality behind the published center-zero square
threshold `q ≥ 77`.

The proof uses the elementary tangent/AM-GM estimate
`2√q ≤ q/9 + 9`, obtained from `(√q - 9)^2 ≥ 0`.
@isnad1 id=lt.1h1v.s6.6514689cbbe6 from=translated src=- shape=d6bed19f vocab=ddb14d56
-/
theorem centerZero_numeric_bound {q : ℕ} (hq : 77 ≤ q) :
    (q : ℝ) - 3 - 2 * Real.sqrt (q : ℝ) > 56 := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hsquare : 0 ≤ (Real.sqrt (q : ℝ) - 9) ^ 2 := sq_nonneg _
  have hqR : (77 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

/-- The numerical inequality used for the cube bound `q ≥ 1037` in
Section 13.  The auxiliary square `(√q - 32)^2 ≥ 0` gives a rational
upper tangent strong enough at the endpoint.
@isnad1 id=lt.1h1v.s5.5eb08902cd70 from=translated src=- shape=95254b68 vocab=ddb14d56
-/
theorem cube_numeric_bound {q : ℕ} (hq : 1037 ≤ q) :
    (q : ℝ) - 28 * Real.sqrt (q : ℝ) > 135 := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hsquare : 0 ≤ (Real.sqrt (q : ℝ) - 32) ^ 2 := sq_nonneg _
  have hqR : (1037 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

/-- The numerical inequality behind the Section 7 threshold
`q ≥ 553736`: equivalently `q - 741√q > 2332`.

The square `(√q - 744)^2 ≥ 0` gives exactly enough rational slack at the
endpoint.
@isnad1 id=lt.1h1v.s5.7461992ea342 from=translated src=- shape=95254b68 vocab=ddb14d56
-/
theorem centerOne_numeric_bound {q : ℕ} (hq : 553736 ≤ q) :
    (q : ℝ) - 741 * Real.sqrt (q : ℝ) > 2332 := by
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hsquare : 0 ≤ (Real.sqrt (q : ℝ) - 744) ^ 2 := sq_nonneg _
  have hqR : (553736 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  nlinarith

end MagicSquares
