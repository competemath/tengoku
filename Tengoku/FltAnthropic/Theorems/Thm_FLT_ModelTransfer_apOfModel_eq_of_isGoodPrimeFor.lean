import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity
import Tengoku.FltAnthropic.P2M.Sol.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] FLT.ModelTransfer.reducedChange_r FLT.ModelTransfer.reducedChange_t FLT.ModelTransfer.reducedChange_s FLT.ModelTransfer.ClearedData.mk.injEq FLT.ModelTransfer.reducedChange_u FLT.ModelTransfer.ClearedData.mk.sizeOf_spec FLT.ModelTransfer.reducedChange_u_inv WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve
namespace FLT.ModelTransfer
theorem apOfModel_eq_of_isGoodPrimeFor {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by exact @_root_.P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor.solution V W C q hq hq2 hq3 hC hV hW
end FLT.ModelTransfer
