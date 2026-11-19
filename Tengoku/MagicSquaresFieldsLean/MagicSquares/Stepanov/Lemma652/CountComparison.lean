import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# The comparison of equations (6.26) and (6.27)

To keep the algebra transparent, this file writes `Q = q/m` as a
separate rational variable.  The two LN97 bounds are then

    S < r Q M + 1/2 r M^2 (k+1) + r M (k+1),

and

    r Q M + r Q (k+1) - 2 r k M ≤ A.

The book observes that the first right-hand side is at most the second
provided

    M^2 + 6M ≤ 2Q,

which itself follows from `(M+3)^2 ≤ 2Q`.
-/

/-- The middle inequality on p. 307.
@isnad1 id=le.4h4v.s8.fe19e035f74d from=translated src=- shape=24cfed24 vocab=08db80dc
-/
theorem ln97_6_52_count_middle_comparison
    (r k M Q : ℚ)
    (hr : 0 ≤ r)
    (hk : 0 ≤ k)
    (hM : 0 ≤ M)
    (hquad : M ^ 2 + 6 * M ≤ 2 * Q) :
    (1 / 2 : ℚ) * r * M ^ 2 * (k + 1) +
        r * M * (k + 1)
      ≤ r * Q * (k + 1) - 2 * r * k * M := by
  have hk1 : 0 ≤ k + 1 := by linarith
  have hscale0 : 0 ≤ (1 / 2 : ℚ) * r * (k + 1) := by
    positivity
  have hs :=
    mul_le_mul_of_nonneg_left hquad hscale0
  have hkstep : k ≤ k + 1 := by linarith
  have hfac : 0 ≤ 2 * r * M := by positivity
  have hkm0 :=
    mul_le_mul_of_nonneg_left hkstep hfac
  have hkm :
      2 * r * k * M ≤ 2 * r * (k + 1) * M := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hkm0
  nlinarith [hs, hkm]

/-- Equations (6.26) and (6.27), together with the quadratic condition,
imply `S < A`.
@isnad1 id=lt.6h6v.s8.ff33a77e4ee3 from=translated src=- shape=e1996bb0 vocab=1eba5f99
-/
theorem ln97_6_52_S_lt_A_of_bounds
    (S A r k M Q : ℚ)
    (hr : 0 ≤ r)
    (hk : 0 ≤ k)
    (hM : 0 ≤ M)
    (hquad : M ^ 2 + 6 * M ≤ 2 * Q)
    (hS :
      S <
        r * Q * M +
          (1 / 2 : ℚ) * r * M ^ 2 * (k + 1) +
          r * M * (k + 1))
    (hA :
      r * Q * M + r * Q * (k + 1) - 2 * r * k * M ≤ A) :
    S < A := by
  have hmid :=
    ln97_6_52_count_middle_comparison
      r k M Q hr hk hM hquad
  linarith

/-- The book's stated hypothesis `(M+3)^2 ≤ 2Q` implies the quadratic
condition used in the comparison.
@isnad1 id=le.1h2v.s6.7facb79ebbff from=translated src=- shape=cbb95c37 vocab=ab2f6e4f
-/
theorem ln97_6_52_rational_shifted_square_implies_quadratic
    (M Q : ℚ)
    (hshift : (M + 3) ^ 2 ≤ 2 * Q) :
    M ^ 2 + 6 * M ≤ 2 * Q := by
  nlinarith

/-- Full p. 307 comparison directly from the shifted-square hypothesis.
@isnad1 id=lt.6h6v.s8.36c452b9de57 from=translated src=- shape=e0b0a32a vocab=1eba5f99
-/
theorem ln97_6_52_S_lt_A_of_shifted_square
    (S A r k M Q : ℚ)
    (hr : 0 ≤ r)
    (hk : 0 ≤ k)
    (hM : 0 ≤ M)
    (hshift : (M + 3) ^ 2 ≤ 2 * Q)
    (hS :
      S <
        r * Q * M +
          (1 / 2 : ℚ) * r * M ^ 2 * (k + 1) +
          r * M * (k + 1))
    (hA :
      r * Q * M + r * Q * (k + 1) - 2 * r * k * M ≤ A) :
    S < A := by
  apply ln97_6_52_S_lt_A_of_bounds S A r k M Q hr hk hM
  · exact ln97_6_52_rational_shifted_square_implies_quadratic M Q hshift
  · exact hS
  · exact hA

end LN97
end MagicSquares
