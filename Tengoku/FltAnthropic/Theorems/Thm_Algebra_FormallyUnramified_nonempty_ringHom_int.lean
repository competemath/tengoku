import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallyUnramified_nonempty_ringHom_int

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallyUnramified_nonempty_ringHom_int.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=nonempty.0h1v.s6.666987985e4f from=translated src=- shape=7cc4a2b9 vocab=555277ab
-/
theorem Algebra.FormallyUnramified.nonempty_ringHom_int
    (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ) := by exact @_root_.P2MW.S_Algebra_FormallyUnramified_nonempty_ringHom_int.solution B _ _ _ _ _
