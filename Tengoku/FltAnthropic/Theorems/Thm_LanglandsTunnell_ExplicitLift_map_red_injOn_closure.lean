import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.Seed.Algebra.Group.Submonoid.Membership
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_ExplicitLift_map_red_injOn_closure.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem LanglandsTunnell.ExplicitLift.map_red_injOn_closure :
    Set.InjOn (fun M : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) => M.map FLT.ExplicitLift.red)
      (Submonoid.closure
        ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) := by exact @_root_.P2MW.S_LanglandsTunnell_ExplicitLift_map_red_injOn_closure.solution
