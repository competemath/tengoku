import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_constantTerm_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_constantTerm_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open AutomorphicForm MeasureTheory
theorem AutomorphicForm.constantTerm_smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) (c : ℂ) (f : G → ℂ) (g : G) :
    AutomorphicForm.constantTerm μ u (fun x => c * f x) g
      = c * AutomorphicForm.constantTerm μ u f g := by exact @_root_.P2MW.S_AutomorphicForm_constantTerm_smul.solution Q _ G _ μ u c f g
