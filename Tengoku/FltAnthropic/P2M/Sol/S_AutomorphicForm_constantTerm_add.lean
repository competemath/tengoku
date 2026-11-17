import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_constantTerm_add.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_constantTerm_add
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) {f₁ f₂ : G → ℂ} (g : G)
    (h₁ : Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : Integrable (constantTermIntegrand u f₂ g) μ) :
    constantTerm μ u (fun x => f₁ x + f₂ x) g
      = constantTerm μ u f₁ g + constantTerm μ u f₂ g := by
  simpa [constantTerm, constantTermIntegrand] using integral_add h₁ h₂
