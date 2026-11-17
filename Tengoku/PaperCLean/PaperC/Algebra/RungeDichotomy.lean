import Tengoku.PaperCLean.PaperC.Algebra.IntegerPolynomialRootBound
import Tengoku.PaperCLean.PaperC.Algebra.RungeTruncation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The final dichotomy in the Runge argument

This file isolates the two elementary conclusions after equation (3.3).

* In the non-equality branch, dyadic separation and a bound `B / U` force
  `U ≤ 2^d B`.
* In the equality branch, an integral root of the nonzero auxiliary
  polynomial is bounded by one plus its height.

The analytic estimate and the construction of the auxiliary polynomial remain
separate inputs.  Keeping this last step explicit prevents the final numerical
argument from being hidden inside asymptotic notation.
-/

namespace PaperC
namespace RungeDichotomy

open scoped Polynomial

/--
An integer separated from a dyadic rational by denominator `2^d`, but at
distance at most `B/U`, forces `U ≤ 2^d B`.
@isnad1 id=le.3h5v.s7.2d8dc8eda9a4 from=translated src=- shape=ec7db171 vocab=dbf3ba04
-/
theorem nat_le_two_pow_mul_of_dyadic_gap_and_tail
    (a b : ℤ) (d U B : ℕ)
    (hU : 1 ≤ U)
    (hne : (a : ℚ) ≠ (b : ℚ) / (2 : ℚ) ^ d)
    (htail :
      |(a : ℚ) - (b : ℚ) / (2 : ℚ) ^ d| ≤
        (B : ℚ) / (U : ℚ)) :
    U ≤ 2 ^ d * B := by
  have hgap :
      1 / (2 : ℚ) ^ d ≤
        |(a : ℚ) - (b : ℚ) / (2 : ℚ) ^ d| :=
    one_div_two_pow_le_abs_integer_sub_dyadic a b d hne
  have hcompare :
      1 / (2 : ℚ) ^ d ≤ (B : ℚ) / (U : ℚ) :=
    hgap.trans htail
  have hpow : (0 : ℚ) < (2 : ℚ) ^ d := by positivity
  have hUq : (0 : ℚ) < (U : ℚ) := by
    exact_mod_cast (show 0 < U by omega)
  have hcross :
      (U : ℚ) ≤ (2 : ℚ) ^ d * (B : ℚ) := by
    have hcross' :=
      (div_le_div_iff₀ hpow hUq).mp hcompare
    simpa [mul_comm] using hcross'
  exact_mod_cast hcross

/--
Specialization of the preceding numerical step to the actual Runge
truncation, using the integral polynomial constructed in
`RungeTruncation`.
@isnad1 id=le.3h5v.s7.44654bee126f from=translated src=- shape=2d9b4f7c vocab=1053e4e5
-/
theorem nat_le_two_pow_mul_of_rungeTruncation_gap
    {k : ℕ} (γ : Fin (2 * k) → ℤ)
    (a : ℤ) (U B : ℕ)
    (hU : 1 ≤ U)
    (hne :
      (a : ℚ) ≠
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ))
    (htail :
      |(a : ℚ) -
        (RungeTruncation.rungeTruncation γ).eval (U : ℚ)| ≤
          (B : ℚ) / (U : ℚ)) :
    U ≤ 2 ^ (2 * k) * B := by
  let p : ℤ[X] := RungeTruncation.integralRungeTruncation γ
  have hscaled :
      (RungeTruncation.rungeTruncation γ).eval (U : ℚ) =
        ((p.eval (U : ℤ) : ℤ) : ℚ) / (2 : ℚ) ^ (2 * k) := by
    simpa [p] using
      RungeTruncation.eval_rungeTruncation_eq_integral_div
        γ (U : ℤ)
  apply nat_le_two_pow_mul_of_dyadic_gap_and_tail
    a (p.eval (U : ℤ)) (2 * k) U B hU
  · simpa [hscaled] using hne
  · simpa [hscaled] using htail

end RungeDichotomy
end PaperC
