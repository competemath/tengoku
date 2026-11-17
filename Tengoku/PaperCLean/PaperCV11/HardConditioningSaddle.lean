import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Paper C v1.1: the hard-conditioning saddle

The hard-conditioning scheme has two normalized exponential envelopes. With
`a = log Y / S_N`, their leading coefficients are `a` and `(2 * a)⁻¹`.
This file proves the exact max-min calculation used in Proposition 3.11.

The arithmetic estimates producing the two envelopes are formalized
separately. The final declaration below is the algebraic v1.1 endpoint and
introduces no new literature input.
-/

namespace PaperC
namespace V11
namespace HardConditioningSaddle

/-- No positive cutoff can make both `B / u` and `u` exceed `sqrt B`.-/
theorem min_div_self_le_sqrt
    {B u : ℝ} (hB : 0 ≤ B) (hu : 0 < u) :
    min (B / u) u ≤ Real.sqrt B := by
  by_cases hsmall : u ≤ Real.sqrt B
  · exact (min_le_right _ _).trans hsmall
  · have hsqrtLe : Real.sqrt B ≤ u := le_of_not_ge hsmall
    have hdiv : B / u ≤ Real.sqrt B := by
      apply (div_le_iff₀ hu).2
      calc
        B = (Real.sqrt B) ^ 2 := (Real.sq_sqrt hB).symm
        _ = Real.sqrt B * Real.sqrt B := by rw [pow_two]
        _ ≤ Real.sqrt B * u :=
          mul_le_mul_of_nonneg_left hsqrtLe (Real.sqrt_nonneg B)
    exact (min_le_left _ _).trans hdiv

end HardConditioningSaddle
end V11

end PaperC
