import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=iff.4h3v.s8.9651786d105e from=translated src=- shape=f020ecbc vocab=f9417824
-/
theorem WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (E : WeierstrassCurve F)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0) (C : WeierstrassCurve.VariableChange F) :
    C • E = E ↔ C = 1 ∨ C = ⟨-1, 0, -E.a₁, -E.a₃⟩ := by exact @_root_.P2MW.S_WeierstrassCurve_variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero.solution F _ h2 h3 E hc₄ hc₆ C
