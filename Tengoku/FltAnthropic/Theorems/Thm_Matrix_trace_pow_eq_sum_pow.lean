import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_trace_pow_eq_sum_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_trace_pow_eq_sum_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Matrix.trace_pow_eq_sum_pow {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (htr : M.trace = α + β) (hdet : M.det = α * β) (k : ℕ) :
    (M ^ k).trace = α ^ k + β ^ k := by exact @_root_.P2MW.S_Matrix_trace_pow_eq_sum_pow.solution R _ M α β htr hdet k
