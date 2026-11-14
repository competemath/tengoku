import Tengoku.Piirrationalitymeasure.Formalization.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Polynomial numerator of the stationary equation in Section 4.2.
-/

namespace PiIrrationality

def phaseNumerator (alpha beta y : ℚ) : ℚ :=
  alpha * (y ^ 2 + 6 * y + 25) * (25 - y) +
    beta * (2 * y + 6) * y * (25 - y) +
    y * (y ^ 2 + 6 * y + 25)

/--
@isnad1 id=eq.0h3v.s4.92ffa4071f0e from=translated src=- shape=7d4988ab vocab=6a21d048
-/
theorem phaseNumerator_eq_neg_stationary (alpha beta y : ℚ) :
    -phaseNumerator alpha beta y = stationaryPolynomial alpha beta y := by
  unfold phaseNumerator stationaryPolynomial
  ring

/--
@isnad1 id=eq.0h1v.s7.f0e60188aecc from=translated src=- shape=dc3867f2 vocab=85ebead5
-/
theorem phaseNumerator_candidate_cleared (y : ℚ) :
    5570 * (-phaseNumerator (1857 / 5570) (3714 / 5570) y) =
      3715 * y^3 - 232119 * y^2 - 928475 * y - 1160625 := by
  rw [phaseNumerator_eq_neg_stationary]
  rw [stationaryPolynomial_candidate_cleared]

end PiIrrationality
