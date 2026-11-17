import Tengoku.Seed.Tactic
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_EisensteinWeightOne_chiNegThree_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_EisensteinWeightOne_chiNegThree_mul

open EisensteinWeightOne

/--
@isnad1 id=eq.0h2v.s4.37976a92f514 from=translated src=- shape=0438c7a3 vocab=30272206
-/
theorem solution (m n : ℕ) :
    chiNegThree (m * n) = chiNegThree m * chiNegThree n := by
  simp only [chiNegThree]
  rw [Nat.mul_mod]
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hm with h | h | h <;> rcases hn with h' | h' | h' <;> rw [h, h'] <;> decide
