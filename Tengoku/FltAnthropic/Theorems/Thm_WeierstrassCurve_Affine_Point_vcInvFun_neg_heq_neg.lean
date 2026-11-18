import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open WeierstrassCurve WeierstrassCurve.Affine
/--
@isnad1 id=heq.0h3v.s8.1782a8961eda from=translated src=- shape=0acd8f44 vocab=09e261f8
-/
theorem WeierstrassCurve.Affine.Point.vcInvFun_neg_heq_neg {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    HEq (Point.vcInvFun (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) W.toAffine P) (-P) := by exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.solution F _ _ W P
