import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Parameters
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.CountComparison
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Counts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# The numerical hypotheses of Lemma 6.52

The number of equations uses the individual derivative bounds.  We derive
the strict dimension inequality from the book's shifted-square hypothesis,
and then simplify the auxiliary polynomial's degree to the stated bound.
-/

/-- Number of scalar equations using the degree bound for each `n`.-/
def stepanovEquationCount (r M D k u : ℕ) : ℕ :=
  r * ∑ n ∈ Finset.range M, (D + n * (k - 1) + u + 1)

theorem twice_sum_linear (M D k u : ℕ) :
    2 * (∑ n ∈ Finset.range M, (D + n * k + u + 1)) + k * M =
      2 * M * (D + u + 1) + k * M ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      nlinarith

/-- The shifted-square condition also controls the integer quotient.-/
theorem ln97_6_52_quadratic_floor {q m M : ℕ} (hm : 0 < m)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * q) :
    M ^ 2 + 6 * M ≤ 2 * (q / m) := by
  have hrem := Nat.mod_lt q hm
  have hdiv := Nat.mod_add_div q m
  have hmul : (M ^ 2 + 6 * M) * m ≤ 2 * (q / m) * m := by
    nlinarith
  exact Nat.le_of_mul_le_mul_right hmul hm

theorem ln97_6_52_parameter_bounds {q m k M : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hM : k + 1 ≤ M)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * q) :
    k ≤ q / m ∧ M ≤ q := by
  have hquad := ln97_6_52_quadratic_floor hm hshift
  have hMfloor : M ≤ q / m := by nlinarith
  exact ⟨by omega, hMfloor.trans (Nat.div_le_self q m)⟩

/-- The literal coefficient count is strictly smaller than the number
of unknowns, with no additional dimension assumption.-/
theorem ln97_6_52_equationCount_lt_unknowns {q m r k M : ℕ}
    (hm : 0 < m) (hr : 0 < r) (hrm : r < m)
    (hk : 0 < k) (hM : k + 1 ≤ M)
    (hshift : (M + 3) ^ 2 * m ≤ 2 * q) :
    stepanovEquationCount r M (q / m - k) k (stepanovU r m M k) <
      m * (stepanovU r m M k + 1) * (q / m - k + 1) := by
  let Q := q / m
  let D := Q - k
  let u := stepanovU r m M k
  have hkQ : k ≤ Q := (ln97_6_52_parameter_bounds hm hk hM hshift).1
  have hD : D + k = Q := Nat.sub_add_cancel hkQ
  have hu := stepanovU_mul_le r m M k
  have hu' := lt_stepanovU_succ_mul r m M k hm
  change u * m ≤ r * (M + k + 1) at hu
  change r * (M + k + 1) < (u + 1) * m at hu'
  have hu_small : u < M + k + 1 := by nlinarith
  have hquad := ln97_6_52_quadratic_floor hm hshift
  have hsum := twice_sum_linear M D (k - 1) u
  have hkm : k - 1 + 1 = k := by omega
  have hS : (stepanovEquationCount r M D k u : ℚ) <
      (r : ℚ) * Q * M + (1 / 2 : ℚ) * r * M ^ 2 * (k + 1) +
        r * M * (k + 1) := by
    have hs : (2 : ℚ) * (∑ n ∈ Finset.range M, (D + n * (k - 1) + u + 1) : ℕ) +
        (k - 1 : ℕ) * M = 2 * M * (D + u + 1) + (k - 1 : ℕ) * (M : ℚ) ^ 2 := by
      exact_mod_cast hsum
    have hd : (D : ℚ) + k = Q := by exact_mod_cast hD
    have hkm' : (k - 1 : ℕ) + (1 : ℚ) = k := by exact_mod_cast hkm
    have huq : (u : ℚ) < M + k + 1 := by exact_mod_cast hu_small
    have hrq : (0 : ℚ) < r := by exact_mod_cast hr
    have hMq : (0 : ℚ) < M := by exact_mod_cast (show 0 < M by omega)
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    have hprod := mul_lt_mul_of_pos_left huq (mul_pos hrq hMq)
    have hnonneg : (0 : ℚ) ≤ r * (k - 1 : ℕ) * M := by positivity
    have hdk := mul_le_mul_of_nonneg_left (show (D : ℚ) + 1 ≤ Q by linarith)
      (le_of_lt (mul_pos hrq hMq))
    unfold stepanovEquationCount
    rw [Nat.cast_mul]
    nlinarith [congrArg (fun x : ℚ => (r : ℚ) * x) hs,
      congrArg (fun x : ℚ => (r : ℚ) * (M : ℚ) ^ 2 * x) hkm']
  have hA : (r : ℚ) * Q * M + r * Q * (k + 1) - 2 * r * k * M ≤
      (m * (u + 1) * (D + 1) : ℕ) := by
    have hd : (D : ℚ) + k = Q := by exact_mod_cast hD
    have huq : (r : ℚ) * (M + k + 1) ≤ (u + 1) * m := by
      exact_mod_cast hu'.le
    have hMq : (k : ℚ) + 1 ≤ M := by exact_mod_cast hM
    have hp := mul_le_mul_of_nonneg_right huq (show (0 : ℚ) ≤ D by positivity)
    have hp' := mul_le_mul_of_nonneg_left hMq (show (0 : ℚ) ≤ r * k by positivity)
    push_cast
    nlinarith [show (0 : ℚ) ≤ m * (u + 1) by positivity]
  have hq : (M : ℚ) ^ 2 + 6 * M ≤ 2 * Q := by exact_mod_cast hquad
  have h := ln97_6_52_S_lt_A_of_bounds
    (stepanovEquationCount r M D k u) (m * (u + 1) * (D + 1))
    r k M Q (by positivity) (by positivity) (by positivity) hq hS (by push_cast at hA; exact hA)
  exact_mod_cast h

/-- The degree estimate on p.308, with its positive denominator cleared.
The weaker bound `M ≤ q` already suffices for the stated constant `4`.-/
theorem ln97_6_52_auxiliary_degree_bound {q m r k M : ℕ}
    (hq : 0 < q) (hm : 0 < m) (hrm : r < m) (hk : 0 < k)
    (hM : M ≤ q) :
    m * (M * k + (q / m - k + q * stepanovU r m M k +
      (m - 1) * (((q - 1) / m) * k))) <
      r * q * M + 4 * k * q * m := by
  let u := stepanovU r m M k
  have hu := stepanovU_mul_le r m M k
  change u * m ≤ r * (M + k + 1) at hu
  have hD : m * (q / m - k) ≤ q := by
    exact (Nat.mul_le_mul_left m (Nat.sub_le (q / m) k)).trans (Nat.mul_div_le q m)
  have hs : m * ((q - 1) / m) ≤ q := (Nat.mul_div_le (q - 1) m).trans (Nat.sub_le q 1)
  have hbase : m * (M * k + (q / m - k + q * u +
      (m - 1) * (((q - 1) / m) * k))) ≤
      m * k * q + q + r * q * (M + k + 1) + (m - 1) * q * k := by
    have h1 := Nat.mul_le_mul_left (m * k) hM
    have h2 := Nat.mul_le_mul_left q hu
    have h3 := Nat.mul_le_mul_left ((m - 1) * k) hs
    nlinarith
  have hpred : m - 1 + 1 = m := by omega
  have hr : r + 1 ≤ m := by omega
  have hmk : m ≤ m * k := Nat.le_mul_of_pos_right m hk
  have hgap : m * k + 1 + r * (k + 1) + (m - 1) * k < 4 * k * m := by
    have h1 := Nat.mul_le_mul_right (k + 1) hr
    nlinarith
  have hfinal := Nat.mul_lt_mul_of_pos_right hgap hq
  dsimp [u] at hbase
  nlinarith

end LN97
end MagicSquares
