import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# Parameter arithmetic at the start of LN97 Theorem 6.53

Theorem 6.53 chooses

    M = floor(sqrt(2q/m)) - 3

and, under `q ≥ 100 m k^2`, derives the coarse lower bounds needed to
apply Lemma 6.52.

This file isolates the elementary real inequalities so that the later
finite-field counting proof does not have to redo them.
`MultiplicityChoice` supplies the integer parameter used in the completed
proof, via the alternative choice `M = ceil(sqrt(q/m))`.
-/

/-- A coarse square-root consequence of `q ≥ 100 m k^2`:
`sqrt(q/m) ≥ 10k`, written without division.
@isnad1 id=le.3h3v.s6.5a007105207d from=translated src=- shape=0a291ba4 vocab=117eaa13
-/
theorem sqrt_q_over_m_ge_ten_k
    (q m k : ℝ)
    (hq : 100 * m * k ^ 2 ≤ q)
    (hm : 0 < m)
    (_hk : 0 ≤ k) :
    10 * k ≤ Real.sqrt (q / m) := by
  have hleft0 : 0 ≤ 100 * m * k ^ 2 := by
    positivity
  have hq0 : 0 ≤ q := by
    linarith
  have hdiv :
      100 * k ^ 2 ≤ q / m := by
    apply (le_div_iff₀ hm).2
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt (q / m) :=
    Real.sqrt_nonneg _
  have hqdiv_nonneg : 0 ≤ q / m :=
    div_nonneg hq0 (le_of_lt hm)
  have hsquare :
      (10 * k) ^ 2 ≤ (Real.sqrt (q / m)) ^ 2 := by
    rw [Real.sq_sqrt hqdiv_nonneg]
    nlinarith
  nlinarith

/-- The book also uses the weaker bound
`sqrt(q/m) ≥ k+1`; it follows once `k ≥ 1`.
@isnad1 id=le.3h3v.s6.db921c22b92e from=translated src=- shape=29a31f18 vocab=d44e7500
-/
theorem sqrt_q_over_m_ge_k_add_one
    (q m k : ℝ)
    (hq : 100 * m * k ^ 2 ≤ q)
    (hm : 0 < m)
    (hk : 1 ≤ k) :
    k + 1 ≤ Real.sqrt (q / m) := by
  have h10 :=
    sqrt_q_over_m_ge_ten_k q m k hq hm
      (le_trans (by norm_num) hk)
  linarith

/-- The shifted-square hypothesis required by Lemma 6.52 is automatic
for the ideal real choice `M = sqrt(2q/m)-3`.
@isnad1 id=eq.2h2v.s7.1fc2d51609ed from=translated src=- shape=5a62edd2 vocab=e7d2045c
-/
theorem shifted_square_of_sqrt_choice
    (q m : ℝ)
    (hm : 0 < m)
    (hq : 0 ≤ q) :
    ((Real.sqrt (2 * q / m) - 3) + 3) ^ 2 = 2 * q / m := by
  have hnum : 0 ≤ 2 * q := by
    positivity
  have hnonneg : 0 ≤ 2 * q / m :=
    div_nonneg hnum (le_of_lt hm)
  rw [sub_add_cancel]
  exact Real.sq_sqrt hnonneg

end LN97
end MagicSquares
