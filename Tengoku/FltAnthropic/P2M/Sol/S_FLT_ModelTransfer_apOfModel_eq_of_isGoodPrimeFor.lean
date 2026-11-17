import Tengoku.FltAnthropic.Definitions.Def_ModelTransfer_ClearedData
import Tengoku.FltAnthropic.Theorems.Thm_FLT_ModelTransfer_exists_clearedData_not_dvd
import Tengoku.FltAnthropic.Theorems.Thm_FLT_ModelTransfer_reducedChange_smul_reductionMod
import Tengoku.FltAnthropic.Theorems.Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

open WeierstrassCurve FLT.ModelTransfer

/--
@isnad1 id=eq.6h4v.s6.ad9ae432eb38 from=translated src=- shape=36feb5e6 vocab=99ef0b6c
-/
theorem solution {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by
  classical
  obtain ⟨D, hD⟩ := exists_clearedData_not_dvd hq hq2 hq3 hC hV hW
  haveI : Fact q.Prime := ⟨hq⟩
  have hred := reducedChange_smul_reductionMod hC D hD
  have hcard : (W.reductionMod q).card = (V.reductionMod q).card :=
    card_eq_of_variableChange_smul_eq hred
  simp only [WeierstrassCurve.apOfModel, WeierstrassCurve.traceOfFrobenius, hcard]
