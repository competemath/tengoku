import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearIndependent_exists_det_submatrix_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearIndependent_exists_det_submatrix_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h4v.s7.fc5fcea374d2 from=translated src=- shape=a9332628 vocab=f5a72ced
-/
theorem LinearIndependent.exists_det_submatrix_ne_zero
    {k : Type*} [Field k] {ι : Type*} {n : ℕ}
    (f : Fin n → ι → k) (hf : LinearIndependent k f) :
    ∃ s : Fin n → ι, Function.Injective s ∧ (Matrix.of fun l j => f j (s l)).det ≠ 0 := by exact @_root_.P2MW.S_LinearIndependent_exists_det_submatrix_ne_zero.solution k _ ι n f hf
