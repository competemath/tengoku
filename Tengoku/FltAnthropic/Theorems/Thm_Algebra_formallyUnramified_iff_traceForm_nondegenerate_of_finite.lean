import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem Algebra.formallyUnramified_iff_traceForm_nondegenerate_of_finite
    (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B] :
    Algebra.FormallyUnramified K B ↔ (Algebra.traceForm K B).Nondegenerate := by exact @_root_.P2MW.S_Algebra_formallyUnramified_iff_traceForm_nondegenerate_of_finite.solution K _ B _ _ _
