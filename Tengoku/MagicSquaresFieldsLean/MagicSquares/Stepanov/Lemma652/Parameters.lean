import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# The floor parameter u in equation (6.23)

LN97 chooses

    u = floor((r/m)(M+k+1)).

For natural-number parameters this is

    u = (r * (M+k+1)) / m.

The two inequalities below are the exact floor inequalities used when
counting the coefficients `A` and equations `S`.
-/

/-- The parameter `u` from equation (6.23).-/
def stepanovU (r m M k : ℕ) : ℕ :=
  (r * (M + k + 1)) / m

/-- Lower-side floor inequality:
`u*m ≤ r*(M+k+1)`.
@isnad1 id=le.0h4v.s5.2ab55967a39d from=translated src=- shape=7eee58c7 vocab=f3a9dc12
-/
theorem stepanovU_mul_le
    (r m M k : ℕ) :
    stepanovU r m M k * m
      ≤ r * (M + k + 1) := by
  simpa [stepanovU] using
    Nat.div_mul_le_self (r * (M + k + 1)) m

/-- Upper-side floor inequality:
`r*(M+k+1) < (u+1)*m`, provided `m>0`.
@isnad1 id=lt.1h4v.s6.ccb9b6b85472 from=translated src=- shape=01426a27 vocab=cebe9d22
-/
theorem lt_stepanovU_succ_mul
    (r m M k : ℕ)
    (hm : 0 < m) :
    r * (M + k + 1)
      < (stepanovU r m M k + 1) * m := by
  have hdiv :
      (r * (M + k + 1)) / m
        < (r * (M + k + 1)) / m + 1 :=
    Nat.lt_succ_self _
  have h :=
    (Nat.div_lt_iff_lt_mul hm).mp hdiv
  simpa [stepanovU] using h

end LN97
end MagicSquares
