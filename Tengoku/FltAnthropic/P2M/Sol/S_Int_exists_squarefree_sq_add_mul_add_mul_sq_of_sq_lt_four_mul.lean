import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Nat_exists_squarefree_sq_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul

set_option autoImplicit false

theorem solution (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat := by
  set D : ℕ := (4 * n - t ^ 2).toNat with hD_def
  have hD1 : 1 ≤ D := by
    have : (1 : ℤ) ≤ 4 * n - t ^ 2 := by omega
    omega
  have hDcast : ((D : ℤ)) = 4 * n - t ^ 2 := by
    rw [hD_def]; exact Int.toNat_of_nonneg (by omega)
  obtain ⟨c, hc1, hsf⟩ := Nat.exists_squarefree_sq_add D hD1
  have hid : ((c : ℤ) - t) ^ 2 + t * ((c : ℤ) - t) * 2 + n * 2 ^ 2 = ((c ^ 2 + D : ℕ) : ℤ) := by
    push_cast [hDcast]; ring
  refine ⟨(c : ℤ) - t, 2, two_ne_zero, ?_, ?_⟩
  · rw [hid, Int.toNat_natCast]; exact hsf
  · rw [hid, Int.toNat_natCast]; nlinarith [sq_nonneg c]
