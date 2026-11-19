import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# Rewriting the error term in Theorem 6.53
-/

/-- `m * (4 k sqrt(m) sqrt(q)) = 4 k (m sqrt(m)) sqrt(q)`.
@isnad1 id=eq.0h3v.s6.ccafda9526ee from=translated src=- shape=d0ac0229 vocab=733e2c61
-/
theorem theorem653_error_rewrite
    (m k q : ℝ) :
    m * (4 * k * Real.sqrt m * Real.sqrt q) =
      4 * k * (m * Real.sqrt m) * Real.sqrt q := by
  ring

/-- For nonnegative `m`, the factor `m*sqrt(m)` is the usual
`m^(3/2)` appearing in LN97 Theorem 6.53.
@isnad1 id=eq.1h1v.s5.c2c4d01d77cb from=translated src=- shape=025340bf vocab=72659d50
-/
theorem mul_sqrt_eq_rpow_three_halves
    (m : ℝ) (hm : 0 ≤ m) :
    m * Real.sqrt m = m ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  calc
    m * m ^ (1 / 2 : ℝ)
        = m ^ (1 : ℝ) * m ^ (1 / 2 : ℝ) := by simp
    _ = m ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
      symm
      exact Real.rpow_add_of_nonneg hm (by norm_num) (by norm_num)
    _ = m ^ (3 / 2 : ℝ) := by norm_num

end LN97
end MagicSquares
