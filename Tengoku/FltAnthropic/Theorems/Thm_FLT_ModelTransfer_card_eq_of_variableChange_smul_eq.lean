import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.NormalForms
import Tengoku.FltAnthropic.P2M.Sol.S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve
namespace FLT.ModelTransfer
theorem card_eq_of_variableChange_smul_eq {K : Type*} [Field K] [DecidableEq K]
    {X Y : WeierstrassCurve K} {E : WeierstrassCurve.VariableChange K} (h : E • X = Y) :
    Y.card = X.card := by exact @_root_.P2MW.S_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq.solution K _ _ X Y E h
end FLT.ModelTransfer
