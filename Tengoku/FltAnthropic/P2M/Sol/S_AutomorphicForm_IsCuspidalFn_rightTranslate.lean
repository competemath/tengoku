import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_constantTerm_rightTranslate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_IsCuspidalFn_rightTranslate.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_IsCuspidalFn_rightTranslate
open AutomorphicForm MeasureTheory

theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (h : G) : IsCuspidalFn μ u (fun x => f (x * h)) :=
  fun g => by rw [constantTerm_rightTranslate]; exact hf (g * h)
