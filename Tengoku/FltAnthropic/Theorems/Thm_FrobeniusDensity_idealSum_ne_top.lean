import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.FltAnthropic.P2M.Sol.S_FrobeniusDensity_idealSum_ne_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ne.1h2v.s5.4a743e78fba6 from=translated src=- shape=dfe627a7 vocab=676cf995
-/
theorem FrobeniusDensity.idealSum_ne_top
    (K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by exact @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution K _ _ s hs
