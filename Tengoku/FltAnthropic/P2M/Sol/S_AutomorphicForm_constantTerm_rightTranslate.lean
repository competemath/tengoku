import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_constantTerm_rightTranslate.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_constantTerm_rightTranslate
open AutomorphicForm MeasureTheory

/--
@isnad1 id=eq.0h7v.s6.14f874795fa3 from=translated src=- shape=034ed002 vocab=91b3cd34
-/
theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (f : G → ℂ) (g h : G) :
    constantTerm μ u (fun x => f (x * h)) g = constantTerm μ u f (g * h) := by
  simp only [constantTerm, constantTermIntegrand, mul_assoc]
