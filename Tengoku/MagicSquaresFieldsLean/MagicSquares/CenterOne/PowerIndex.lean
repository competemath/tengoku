import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.PowerExistence
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

/-- The index of the subgroup of nonzero `n`th powers in a finite field.-/
def powerIndex (n q : ℕ) : ℕ := Nat.gcd n (q - 1)

/-- For a positive exponent `n`, the power index is positive.
@isnad1 id=lt.1h2v.s4.c17c3b43c7ab from=translated src=- shape=334a1355 vocab=e3c511cd
-/
theorem powerIndex_pos
    {n q : ℕ}
    (hn : 0 < n) :
    0 < powerIndex n q := by
  unfold powerIndex
  exact Nat.gcd_pos_of_pos_left (q - 1) hn

/-- For a positive exponent, the power index is at most the exponent.
@isnad1 id=le.1h2v.s4.a08c9734fdc3 from=translated src=- shape=c048c019 vocab=28bcd665
-/
theorem powerIndex_le_left
    (n q : ℕ)
    (hn : 0 < n) :
    powerIndex n q ≤ n := by
  unfold powerIndex
  exact Nat.gcd_le_left (q - 1) hn

end MagicSquares
