import Tengoku.Seed.NumberTheory.Height.NumberField
import Tengoku.FltAnthropic.P2M.Sol.S_Height_logHeight_algebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Height_logHeight_algebraMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h4v.s7.4001183ffd02 from=translated src=- shape=1d38e416 vocab=aa60c161
-/
theorem Height.logHeight_algebraMap {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {ι : Type*} [Finite ι] (x : ι → K) :
    logHeight (fun i => algebraMap K L (x i))
      = (Module.finrank K L : ℝ) * logHeight x := by exact @_root_.P2MW.S_Height_logHeight_algebraMap.solution K L _ _ _ _ _ ι _ x
