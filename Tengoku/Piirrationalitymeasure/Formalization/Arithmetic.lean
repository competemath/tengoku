import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.PiIrrationality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Elementary algebra for the shifted rational function in Section 2 of the
paper.  These identities are deliberately proved over `ℤ` or `ℚ`; later
modules can reuse them without unfolding the analytic definitions.
-/

namespace PiIrrationality

theorem shifted_quartic (t : ℤ) :
    ((t + 1)^2 + 4) * ((t - 1)^2 + 4) = t^4 + 6 * t^2 + 25 := by
  ring

theorem shifted_quartic_rat (t : ℚ) :
    ((t + 1)^2 + 4) * ((t - 1)^2 + 4) = t^4 + 6 * t^2 + 25 := by
  ring

theorem shifted_poles (t : ℤ) : (t + 5) * (t - 5) = t^2 - 25 := by
  ring

theorem shifted_poles_rat (t : ℚ) : (t + 5) * (t - 5) = t^2 - 25 := by
  ring

def rationalFunction (n : ℕ) (t : ℚ) : ℚ :=
  5 * t ^ (2 * 1857 * n) * (t^4 + 6 * t^2 + 25) ^ (3714 * n) /
    (25 - t^2) ^ (5570 * n + 1)

theorem rationalFunction_even (n : ℕ) (t : ℚ) :
    rationalFunction n (-t) = rationalFunction n t := by
  have hpow : (-t) ^ (2 * 1857 * n) = t ^ (2 * 1857 * n) :=
    Even.neg_pow (n := 2 * 1857 * n) (by
      exact ⟨1857 * n, by ring⟩) t
  unfold rationalFunction
  rw [show (-t)^2 = t^2 by ring, show (-t)^4 = t^4 by ring]
  simp only [rationalFunction, hpow]

theorem candidate_exponent_identities :
    1857 + 3714 - 5570 = 1 ∧
    4 * 3714 - 2 * 5570 = 3716 ∧
    2 * 1857 + 4 * 3714 - 2 * 5570 = 7430 := by
  norm_num

def mobius (z : ℚ) : ℚ := -5 * (1 + z) / (1 - z)

def P (z : ℚ) : ℚ :=
  (z^2 + 2*z + 2) * (2*z^2 + 2*z + 1)

theorem mobius_denominator (z : ℚ) (hz : z ≠ 1) :
    25 - mobius z ^ 2 = -100 * z / (1 - z)^2 := by
  unfold mobius
  field_simp [hz]
  ring

theorem mobius_quartic (z : ℚ) (hz : z ≠ 1) :
    mobius z ^ 4 + 6 * mobius z ^ 2 + 25 =
      400 * P z / (1 - z)^4 := by
  unfold mobius P
  field_simp [hz]
  ring

theorem P_expanded (z : ℚ) :
    P z = 2 + 6*z + 9*z^2 + 6*z^3 + 2*z^4 := by
  unfold P
  ring

def stationaryPolynomial (alpha beta y : ℚ) : ℚ :=
  (alpha + 2 * beta - 1) * y^3
    - (19 * alpha + 44 * beta + 6) * y^2
    - (125 * alpha + 150 * beta + 25) * y
    - 625 * alpha

theorem stationaryPolynomial_candidate (y : ℚ) :
    stationaryPolynomial (1857 / 5570) (3714 / 5570) y =
      (3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625) / 5570 := by
  unfold stationaryPolynomial
  ring

theorem stationaryPolynomial_candidate_cleared (y : ℚ) :
    5570 * stationaryPolynomial (1857 / 5570) (3714 / 5570) y =
      3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625 := by
  rw [stationaryPolynomial_candidate]
  ring

theorem mobius_numerator_nonnegative (z : ℚ) (hz : 0 ≤ z) :
    0 ≤ 2 + 6*z + 9*z^2 + 6*z^3 + 2*z^4 := by
  positivity

def PReal (z : ℝ) : ℝ :=
  2 + 6 * z + 9 * z^2 + 6 * z^3 + 2 * z^4

theorem PReal_strictPositive (z : ℝ) (hz : 0 ≤ z) : 0 < PReal z := by
  dsimp [PReal]
  have h2 : 0 ≤ z ^ 2 := sq_nonneg z
  have h3 : 0 ≤ z ^ 3 := pow_nonneg hz 3
  have h4 : 0 ≤ z ^ 4 := pow_nonneg hz 4
  nlinarith

theorem integer_chamber_certificate :
    (1857 + 3714 ≥ 5570 + 1) ∧
    (2 * 3714 > 5570) ∧
    (7 * 3714 ≤ 5 * 5570 - 1) ∧
    (2 * 1857 + 4 * 3714 - 2 * 5570 ≥ 5570 + 1) := by
  norm_num

/- The four strict chamber margins at the selected parameter point, as in
   equation (6.53). -/
theorem candidate_chamber_margins :
    (1857 : ℚ) / 5570 + 1857 / 2785 - 1 = 1 / 5570 ∧
    2 * (1857 : ℚ) / 2785 - 1 = 929 / 2785 ∧
    5 - 7 * (1857 : ℚ) / 2785 = 926 / 2785 ∧
    2 * (1857 : ℚ) / 5570 + 4 * (1857 : ℚ) / 2785 - 3 = 186 / 557 := by
  norm_num

theorem candidate_chamber_margins_positive :
    0 < (1 : ℚ) / 5570 ∧
    0 < (929 : ℚ) / 2785 ∧
    0 < (926 : ℚ) / 2785 ∧
    0 < (186 : ℚ) / 557 := by
  norm_num

end PiIrrationality
