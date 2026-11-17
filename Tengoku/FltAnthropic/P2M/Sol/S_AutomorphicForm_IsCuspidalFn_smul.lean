import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_constantTerm_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_IsCuspidalFn_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_IsCuspidalFn_smul
open AutomorphicForm MeasureTheory

/--
@isnad1 id=iscuspid.1h6v.s5.8f82ff6c4bc3 from=translated src=- shape=30bb4edd vocab=16f76691
-/
theorem solution {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (c : ℂ) : IsCuspidalFn μ u (fun x => c * f x) :=
  fun g => by rw [constantTerm_smul, hf g, mul_zero]
