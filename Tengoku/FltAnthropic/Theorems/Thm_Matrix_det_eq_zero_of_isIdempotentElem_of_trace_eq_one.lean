import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Matrix.det_eq_zero_of_isIdempotentElem_of_trace_eq_one {A : Type*} [CommRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : IsIdempotentElem e) (htr : e.trace = 1) :
    e.det = 0 := by exact @_root_.P2MW.S_Matrix_det_eq_zero_of_isIdempotentElem_of_trace_eq_one.solution A _ e he htr
