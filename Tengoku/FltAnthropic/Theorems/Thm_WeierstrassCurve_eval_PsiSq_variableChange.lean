import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_eval_PsiSq_variableChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_eval_PsiSq_variableChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h5v.s8.9c98ddf69511 from=translated src=- shape=ca5818b9 vocab=31185d74
-/
theorem WeierstrassCurve.eval_PsiSq_variableChange {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (n : ℤ) (x : R) :
    ((C • W).ΨSq n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (n.natAbs ^ 2 - 1)) * (W.ΨSq n).eval x := by exact @_root_.P2MW.S_WeierstrassCurve_eval_PsiSq_variableChange.solution R _ W C n x
