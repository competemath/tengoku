import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma653.Parameters
import Tengoku.Seed.Algebra.Order.Floor.Semiring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

/-!
# Choosing the integer multiplicity for Theorem 6.53

We use `M = ceil(sqrt(q/m))`.  Under `q ≥ 100 m k²`, this choice satisfies
`M ≥ k+1` and `(M+3)² m ≤ 2q`, and retains the book's error constant.
This avoids a second square root in the rounding argument.
-/

noncomputable def theorem653Multiplicity (q m : ℕ) : ℕ :=
  ⌈Real.sqrt ((q : ℝ) / m)⌉₊

theorem theorem653Multiplicity_spec {q m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (hq : 100 * m * k ^ 2 ≤ q) :
    k + 1 ≤ theorem653Multiplicity q m ∧
    (theorem653Multiplicity q m + 3) ^ 2 * m ≤ 2 * q ∧
    Real.sqrt ((q : ℝ) / m) ≤ theorem653Multiplicity q m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hqR : 100 * (m : ℝ) * (k : ℝ) ^ 2 ≤ q := by exact_mod_cast hq
  let s := Real.sqrt ((q : ℝ) / m)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs10 : 10 ≤ s := by
    have h := sqrt_q_over_m_ge_ten_k q m k hqR hmR (by positivity)
    dsimp [s]; linarith
  have hsq : s ^ 2 = (q : ℝ) / m := Real.sq_sqrt (by positivity)
  have hlow : s ≤ (theorem653Multiplicity q m : ℝ) := Nat.le_ceil s
  have hupp : (theorem653Multiplicity q m : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
  refine ⟨?_, ?_, hlow⟩
  · have h := sqrt_q_over_m_ge_k_add_one q m k hqR hmR hkR
    have : (k : ℝ) + 1 ≤ theorem653Multiplicity q m := h.trans hlow
    exact_mod_cast this
  · have hbound : ((theorem653Multiplicity q m : ℝ) + 3) ^ 2 ≤ 2 * s ^ 2 := by
      have hnonneg : (0 : ℝ) ≤ theorem653Multiplicity q m := by positivity
      nlinarith
    rw [hsq] at hbound
    have h := mul_le_mul_of_nonneg_right hbound hmR.le
    have heq : 2 * ((q : ℝ) / m) * m = 2 * q := by field_simp
    rw [heq] at h
    exact_mod_cast h

end LN97
end MagicSquares
