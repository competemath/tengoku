import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Nat_exists_squarefree_sq_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Nat_exists_squarefree_sq_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h1v.s5.5fbfc844d28e from=translated src=- shape=b20f0f5d vocab=97b8a9eb
-/
theorem Nat.exists_squarefree_sq_add (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D) := by exact @_root_.P2MW.S_Nat_exists_squarefree_sq_add.solution D hD
