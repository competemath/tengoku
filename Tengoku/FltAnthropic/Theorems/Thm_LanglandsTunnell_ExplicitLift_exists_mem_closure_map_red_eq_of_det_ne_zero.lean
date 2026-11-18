import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.Seed.Algebra.Group.Submonoid.Membership
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.1h1v.s9.647552c3a9ca from=translated src=- shape=fd26a6b8 vocab=ba051d8c
-/
theorem LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (hg : g.det ≠ 0) :
    ∃ M ∈ Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2)))),
      M.map FLT.ExplicitLift.red = g := by exact @_root_.P2MW.S_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero.solution g hg
