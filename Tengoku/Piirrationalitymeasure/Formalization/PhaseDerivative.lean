import Tengoku.Piirrationalitymeasure.Formalization.Phase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The rational phase derivative and its denominator-cleared stationary equation.
-/

namespace PiIrrationality

def phaseDerivative (alpha beta y : ℚ) : ℚ :=
  alpha / y + beta * (2 * y + 6) / (y ^ 2 + 6 * y + 25) + 1 / (25 - y)

theorem phaseDerivative_cleared (alpha beta y : ℚ)
    (hy : y ≠ 0) (hquad : y ^ 2 + 6 * y + 25 ≠ 0) (h25 : 25 - y ≠ 0) :
    y * (y ^ 2 + 6 * y + 25) * (25 - y) * phaseDerivative alpha beta y =
      phaseNumerator alpha beta y := by
  unfold phaseDerivative phaseNumerator
  have hquad' : 25 + y * 6 + y ^ 2 ≠ 0 := by
    intro hz
    apply hquad
    linarith
  have hrewrite : y ^ 2 + 6 * y + 25 = 25 + y * 6 + y ^ 2 := by
    ring
  rw [hrewrite]
  field_simp [hy, hquad, hquad', h25]

theorem phaseDerivative_cleared_candidate {y : ℚ}
    (hy : y ≠ 0) (hquad : y ^ 2 + 6 * y + 25 ≠ 0) (h25 : 25 - y ≠ 0) :
    -5570 * y * (y ^ 2 + 6 * y + 25) * (25 - y) *
        phaseDerivative (1857 / 5570) (3714 / 5570) y =
      3715 * y ^ 3 - 232119 * y ^ 2 - 928475 * y - 1160625 := by
  calc
    -5570 * y * (y ^ 2 + 6 * y + 25) * (25 - y) *
          phaseDerivative (1857 / 5570) (3714 / 5570) y =
        -5570 * (y * (y ^ 2 + 6 * y + 25) * (25 - y) *
          phaseDerivative (1857 / 5570) (3714 / 5570) y) := by ring
    _ = -5570 * phaseNumerator (1857 / 5570) (3714 / 5570) y := by
      rw [phaseDerivative_cleared _ _ y hy hquad h25]
    _ = 3715 * y ^ 3 - 232119 * y ^ 2 - 928475 * y - 1160625 := by
      have hc := phaseNumerator_candidate_cleared y
      nlinarith [hc]

theorem phaseDerivative_candidate_eq_zero_iff {y : ℚ}
    (hy : y ≠ 0) (hquad : y ^ 2 + 6 * y + 25 ≠ 0) (h25 : 25 - y ≠ 0) :
    phaseDerivative (1857 / 5570) (3714 / 5570) y = 0 ↔
      3715 * y ^ 3 - 232119 * y ^ 2 - 928475 * y - 1160625 = 0 := by
  have hfactor :
      -5570 * y * (y ^ 2 + 6 * y + 25) * (25 - y) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hy) hquad) h25
  constructor
  · intro hd
    have hc := phaseDerivative_cleared_candidate hy hquad h25
    rw [hd] at hc
    simpa using hc.symm
  · intro hc
    have hcleared := phaseDerivative_cleared_candidate hy hquad h25
    have hz :
        (-5570 * y * (y ^ 2 + 6 * y + 25) * (25 - y)) *
            phaseDerivative (1857 / 5570) (3714 / 5570) y = 0 := by
      rw [hcleared, hc]
    exact (mul_eq_zero.mp hz).resolve_left hfactor

theorem stationaryCubic_ne_zero_at_zero :
    (3715 * (0 : ℚ) ^ 3 - 232119 * (0 : ℚ) ^ 2 - 928475 * (0 : ℚ) - 1160625) ≠ 0 := by
  norm_num

theorem stationaryCubic_ne_zero_at_twentyfive :
    (3715 * (25 : ℚ) ^ 3 - 232119 * (25 : ℚ) ^ 2 - 928475 * (25 : ℚ) - 1160625) ≠ 0 := by
  norm_num

theorem phaseDerivative_candidate_at_66_neg :
    phaseDerivative (1857 / 5570) (3714 / 5570) (66 : ℚ) < 0 := by
  norm_num [phaseDerivative]

theorem phaseDerivative_candidate_at_67_pos :
    0 < phaseDerivative (1857 / 5570) (3714 / 5570) (67 : ℚ) := by
  norm_num [phaseDerivative]

end PiIrrationality
