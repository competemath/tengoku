import Tengoku.AbelFormalization.AbelFormalization.AnalyticMultiplicity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Factorial-normalized polynomial coefficients and jets

The manuscript writes its interpolant as `Σ a_j z^j / j!`. This module
identifies those coefficients with the polynomial's derivatives at zero and
proves the corresponding evaluation formula for every derivative.
-/

noncomputable section

namespace AbelFormalization

open Polynomial

def normalizedCoeff (P : ℂ[X]) (j : ℕ) : ℂ := (j.factorial : ℂ) * P.coeff j

end AbelFormalization
