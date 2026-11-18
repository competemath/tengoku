import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u
theorem Matrix.exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one {A : Type u} [CommRing A] [IsLocalRing A]
    {e : Matrix (Fin 2) (Fin 2) A} (he : e * e = e) (htr : e.trace = 1) :
    ∃ u w : Fin 2 → A, IsUnit (Matrix.of (fun i j => ![u, w] j i)).det ∧
      e.mulVec u = u ∧ e.mulVec w = 0 := by exact @_root_.P2MW.S_Matrix_exists_mulVec_eq_and_isUnit_det_of_isIdempotentElem_of_trace_eq_one.solution A _ _ e he htr
