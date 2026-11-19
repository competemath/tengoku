import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# Numerical heart of LN97 Theorem 6.53

Write

    A = 4 k sqrt(m) sqrt(q).

Equation (6.28), applied with `r=1` and `r=m-1`, gives

    t0+t1 < q/m + A,
    t0+t2 < (m-1)q/m + A.

Together with Lemma 6.45 these inequalities imply

    |N-q| < m A = 4 k m^(3/2) sqrt(q).

Since the actual parameter `m` is a positive natural number, the upper
bound uses the explicit real hypothesis `1 ≤ m`.
-/

/-- Upper half of (6.29).-/
theorem theorem653_upper_arithmetic
    (q m N t0 t1 A : ℝ)
    (hm : 0 < m)
    (hm1 : 1 ≤ m)
    (hN : N = t0 + m * t1)
    (h01 : t0 + t1 < q / m + A)
    (ht0 : 0 ≤ t0) :
    N < q + m * A := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hmul0 := mul_lt_mul_of_pos_left h01 hm
  have hqm : m * (q / m) = q := by
    field_simp [hmne]
  have hmul : m * t0 + m * t1 < q + m * A := by
    calc
      m * t0 + m * t1 = m * (t0 + t1) := by ring
      _ < m * (q / m + A) := hmul0
      _ = q + m * A := by rw [mul_add, hqm]
  have hNle : N ≤ m * t0 + m * t1 := by
    rw [hN]
    nlinarith
  linarith

/-- Lower half from the second choice of `B`.-/
theorem theorem653_lower_arithmetic
    (q m N t0 t1 t2 A : ℝ)
    (hm : 0 < m)
    (hN : N = t0 + m * t1)
    (hpart : t0 + t1 + t2 = q)
    (h02 : t0 + t2 < (m - 1) * q / m + A)
    (ht0 : 0 ≤ t0) :
    q - m * A < N := by
  have hmne : m ≠ 0 := ne_of_gt hm
  have hmul0 := mul_lt_mul_of_pos_left h02 hm
  have hdiv : m * (((m - 1) * q) / m) = (m - 1) * q := by
    field_simp [hmne]
  have hmul :
      m * t0 + m * t2 < (m - 1) * q + m * A := by
    calc
      m * t0 + m * t2 = m * (t0 + t2) := by ring
      _ < m * (((m - 1) * q) / m + A) := hmul0
      _ = (m - 1) * q + m * A := by rw [mul_add, hdiv]
  nlinarith

/-- Combine the two one-sided estimates into the absolute-value form of
Theorem 6.53.-/
theorem theorem653_abs_arithmetic
    (q m N t0 t1 t2 A : ℝ)
    (hm : 0 < m)
    (hm1 : 1 ≤ m)
    (hN : N = t0 + m * t1)
    (hpart : t0 + t1 + t2 = q)
    (h01 : t0 + t1 < q / m + A)
    (h02 : t0 + t2 < (m - 1) * q / m + A)
    (ht0 : 0 ≤ t0) :
    |N - q| < m * A := by
  have hu := theorem653_upper_arithmetic
    q m N t0 t1 A hm hm1 hN h01 ht0
  have hl := theorem653_lower_arithmetic
    q m N t0 t1 t2 A hm hN hpart h02 ht0
  rw [abs_lt]
  constructor <;> linarith

end LN97
end MagicSquares
