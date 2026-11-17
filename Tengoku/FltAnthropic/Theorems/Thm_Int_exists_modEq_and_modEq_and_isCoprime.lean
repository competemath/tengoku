import Tengoku.Seed.Data.Int.GCD
import Tengoku.Seed.Data.Int.ModEq
import Tengoku.Seed.RingTheory.Coprime.Lemmas
import Tengoku.FltAnthropic.P2M.Sol.S_Int_exists_modEq_and_modEq_and_isCoprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Int_exists_modEq_and_modEq_and_isCoprime.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Int.exists_modEq_and_modEq_and_isCoprime {n c d : ℤ}
    (h : ∃ x y z : ℤ, x * c + y * d + z * n = 1) :
    ∃ c' d' : ℤ, c' ≡ c [ZMOD n] ∧ d' ≡ d [ZMOD n] ∧ IsCoprime c' d' := by exact @_root_.P2MW.S_Int_exists_modEq_and_modEq_and_isCoprime.solution n c d h
