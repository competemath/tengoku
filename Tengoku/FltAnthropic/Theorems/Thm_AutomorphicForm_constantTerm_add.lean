import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_constantTerm_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_constantTerm_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
open AutomorphicForm MeasureTheory
/--
@isnad1 id=eq.2h7v.s7.6440bfa04334 from=translated src=- shape=e61178cb vocab=04ae24d2
-/
theorem AutomorphicForm.constantTerm_add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : MeasureTheory.Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₁ g) μ)
    (h₂ : MeasureTheory.Integrable (AutomorphicForm.constantTermIntegrand u f₂ g) μ) :
    AutomorphicForm.constantTerm μ u (fun x => f₁ x + f₂ x) g
      = AutomorphicForm.constantTerm μ u f₁ g + AutomorphicForm.constantTerm μ u f₂ g := by exact @_root_.P2MW.S_AutomorphicForm_constantTerm_add.solution Q _ G _ μ u f₁ f₂ g h₁ h₂
