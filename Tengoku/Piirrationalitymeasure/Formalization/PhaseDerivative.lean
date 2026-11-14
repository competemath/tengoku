import Tengoku.Piirrationalitymeasure.Formalization.Phase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The rational phase derivative and its denominator-cleared stationary equation.
-/

namespace PiIrrationality

def phaseDerivative (alpha beta y : ℚ) : ℚ :=
  alpha / y + beta * (2 * y + 6) / (y ^ 2 + 6 * y + 25) + 1 / (25 - y)

/--
@isnad1 id=eq.3h3v.s7.c7ae3dd54978 from=translated src=- shape=92d73fd2 vocab=e0095055
-/
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

/--
@isnad1 id=eq.3h1v.s8.6d5040655da9 from=translated src=- shape=e1a92586 vocab=1c24813d
-/
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

/--
@isnad1 id=iff.3h1v.s7.4dc7fe0bd33b from=translated src=- shape=ac4f73d6 vocab=db1e3567
-/
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

/--
@isnad1 id=ne.0h0v.s6.617e2879b9a2 from=translated src=- shape=649723c7 vocab=19a3384a
-/
theorem stationaryCubic_ne_zero_at_zero :
    (3715 * (0 : ℚ) ^ 3 - 232119 * (0 : ℚ) ^ 2 - 928475 * (0 : ℚ) - 1160625) ≠ 0 := by
  norm_num

/--
@isnad1 id=ne.0h0v.s6.ee442c1d754d from=translated src=- shape=649723c7 vocab=19a3384a
-/
theorem stationaryCubic_ne_zero_at_twentyfive :
    (3715 * (25 : ℚ) ^ 3 - 232119 * (25 : ℚ) ^ 2 - 928475 * (25 : ℚ) - 1160625) ≠ 0 := by
  norm_num

/--
@isnad1 id=lt.0h0v.s5.1eff050c141b from=translated src=- shape=acebe9c5 vocab=199201d7
-/
theorem phaseDerivative_candidate_at_66_neg :
    phaseDerivative (1857 / 5570) (3714 / 5570) (66 : ℚ) < 0 := by
  norm_num [phaseDerivative]

/--
@isnad1 id=lt.0h0v.s5.3a25a3e896bf from=translated src=- shape=6d78dcd3 vocab=199201d7
-/
theorem phaseDerivative_candidate_at_67_pos :
    0 < phaseDerivative (1857 / 5570) (3714 / 5570) (67 : ℚ) := by
  norm_num [phaseDerivative]

end PiIrrationality
