import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Int_exists_pos_and_not_isSquare_sq_sub_mul_add_of_sq_lt_four_mul

set_option autoImplicit false

namespace U1a_8

/--
@isnad1 id=ex.1h2v.s7.20b83655d1c9 from=translated src=- shape=29b5a3de vocab=e67a7f92
-/
theorem exists_shift (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k * k - t * k + n ∧ ¬ IsSquare (k * k - t * k + n) ∧ (t - 2 * k) ^ 2 < 4 * (k * k - t * k + n) := by
  set D : ℤ := 4 * n - t ^ 2 with hD
  have hD0 : 0 < D := by omega
  refine ⟨D + |t|, ?_, ?_, ?_⟩
  · nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (2 * (D + |t|) - t)]
  · rintro ⟨s, hs⟩
    set m : ℤ := 2 * (D + |t|) - t with hm
    have hmD : D < m := by
      have := abs_nonneg t; have := le_abs_self t; have := neg_abs_le t; omega
    have h4 : 4 * (s * s) = m * m + D := by rw [← hs, hm, hD]; ring
    rcases le_or_gt (2 * |s|) m with h | h
    · nlinarith [sq_abs s, abs_nonneg s]
    · nlinarith [sq_abs s, abs_nonneg s]
  · nlinarith [abs_nonneg t, sq_abs t]

end U1a_8

/--
@isnad1 id=ex.1h2v.s7.2965d2c9ce92 from=translated src=- shape=46e8ad5e vocab=e67a7f92
-/
theorem solution
    (t n : ℤ) (htn : t ^ 2 < 4 * n) :
    ∃ k : ℤ, 0 < k ^ 2 - t * k + n ∧ ¬ IsSquare (k ^ 2 - t * k + n) := by
  obtain ⟨k, h1, h2, -⟩ := U1a_8.exists_shift t n htn
  exact ⟨k, by rw [sq]; exact h1, by rw [sq]; exact h2⟩
