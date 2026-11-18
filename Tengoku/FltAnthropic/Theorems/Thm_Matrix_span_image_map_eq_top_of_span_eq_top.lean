import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Data.Matrix.Basis
import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.LocalRing.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_span_image_map_eq_top_of_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_span_image_map_eq_top_of_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem Matrix.span_image_map_eq_top_of_span_eq_top
    {n : Type*} [Fintype n] [DecidableEq n]
    {k : Type*} [Field k] {K : Type*} [Field K] (f : k →+* K)
    {S : Set (Matrix n n k)} (hS : Submodule.span k S = ⊤) :
    Submodule.span K ((fun X : Matrix n n k => X.map f) '' S) = ⊤ := by exact @_root_.P2MW.S_Matrix_span_image_map_eq_top_of_span_eq_top.solution n _ _ k _ K _ f S hS
