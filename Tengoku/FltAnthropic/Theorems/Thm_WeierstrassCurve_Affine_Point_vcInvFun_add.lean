import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Tengoku.FltAnthropic.P2M.Sol.S_WeierstrassCurve_Affine_Point_vcInvFun_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WeierstrassCurve_Affine_Point_vcInvFun_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=eq.0h5v.s8.7767ccd56901 from=translated src=- shape=7c935748 vocab=50ebe054
-/
theorem WeierstrassCurve.Affine.Point.vcInvFun_add {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve.Affine K) (P Q : W.Point) :
    WeierstrassCurve.Affine.Point.vcInvFun C W (P + Q) =
      WeierstrassCurve.Affine.Point.vcInvFun C W P + WeierstrassCurve.Affine.Point.vcInvFun C W Q := by exact @_root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_add.solution K _ _ C W P Q
