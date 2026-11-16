import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Fin_exists_chain_append

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Fin_exists_chain_append.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.2h5v.s8.e3115c0a1b73 from=translated src=- shape=2d3b7dd0 vocab=3e944ac0
-/
theorem Fin.exists_chain_append {α : Type*} (S : α → α → Prop) {a b c : α}
    (h₁ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = b ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ))
    (h₂ : ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = b ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ)) :
    ∃ (n : ℕ) (f : Fin (n + 1) → α), f 0 = a ∧ f (Fin.last n) = c ∧
      ∀ i : Fin n, S (f i.castSucc) (f i.succ) := by exact @_root_.P2MW.S_Fin_exists_chain_append.solution α S a b c h₁ h₂
