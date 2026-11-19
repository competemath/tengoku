import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# Arithmetic core of LN97 Lemma 6.52, equations (6.26)--(6.27)

The final numerical step on p. 307 is

    (M + 3)^2 <= 2q/m
      ==> M^2 + 6M <= 2q/m.

To avoid introducing rational-valued division into the natural-number
formalization, we clear the positive denominator `m` and use

    (M + 3)^2 * m <= 2q.

The theorem below proves exactly the implication used in the book.
-/

/-- The hypothesis `(M+3)^2 ≤ 2q/m`, with denominators cleared,
implies the weaker quadratic inequality `M^2+6M ≤ 2q/m`.
@isnad1 id=le.1h3v.s6.6725fd48e56c from=translated src=- shape=7dd676d1 vocab=f96c6fce
-/
theorem ln97_6_52_shifted_square_implies_quadratic
    (M q m : ℕ)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * q) :
    (M ^ 2 + 6 * M) * m ≤ 2 * q := by
  have hbase : M ^ 2 + 6 * M ≤ (M + 3) ^ 2 := by
    nlinarith
  exact le_trans (Nat.mul_le_mul_right m hbase) hshift

/-- A convenient factored version of the same estimate.  It is useful
after the common positive factors `r` and `k+1` have been restored in
the coefficient-count comparison.
@isnad1 id=le.1h5v.s7.8978aa175c99 from=translated src=- shape=e9bfb150 vocab=f96c6fce
-/
theorem ln97_6_52_shifted_square_implies_scaled_quadratic
    (M q m r k : ℕ)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * q) :
    (r * (k + 1)) * ((M ^ 2 + 6 * M) * m)
      ≤ (r * (k + 1)) * (2 * q) := by
  exact Nat.mul_le_mul_left _
    (ln97_6_52_shifted_square_implies_quadratic M q m hshift)

end LN97
end MagicSquares
