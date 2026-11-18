import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ModuliPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg

open _root_.WeierstrassCurve open _root_.WeierstrassCurve.Affine

namespace WeierstrassCurve
export _root_.WeierstrassCurve (Affine Affine.negY a₃ a₁ variableChange_a₃ variableChange_a₆ variableChange_a₂ toAffine Affine.Point variableChange_a₁ variableChange_a₄ VariableChange Affine.Point.neg_some)
namespace Affine
export _root_.WeierstrassCurve.Affine (negY Point Point.neg_some vcXInv vcYInv Point.vcInvFun)
namespace Point
export _root_.WeierstrassCurve.Affine.Point (some zero neg_some vcInvFun)
open _root_.WeierstrassCurve.Affine.Point open _root_.WeierstrassCurve.Affine open _root_.WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F]

/--
@isnad1 id=eq.0h2v.s7.e0b5c68bccd6 from=translated src=- shape=4f356614 vocab=bed5a380
-/
theorem negVariableChange_smul' (W : WeierstrassCurve F) :
    (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) • W = W := by
  ext
  · simp only [variableChange_a₁, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₂, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₃, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₄, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₆, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring

end WeierstrassCurve.Affine.Point

open _root_.WeierstrassCurve open _root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve open _root_.WeierstrassCurve.Affine open _root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve.Affine open _root_.WeierstrassCurve.Affine.Point open _root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve.Affine.Point

/--
@isnad1 id=heq.0h3v.s8.1782a8961eda from=translated src=- shape=0acd8f44 vocab=09e261f8
-/
theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    HEq (vcInvFun (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) W.toAffine P) (-P) := by
  have hW : ((⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) • W).toAffine = W.toAffine := negVariableChange_smul' W
  cases P with
  | zero => exact ModularCurve.Point.heq_zero hW
  | some x y h =>
    rw [Affine.Point.neg_some]
    simp only [vcInvFun]
    refine ModularCurve.Point.heq_some hW ?_ ?_
    · simp [vcXInv]
    · simp only [vcYInv, Affine.negY, inv_neg, inv_one, Units.val_neg, Units.val_one, sub_zero]
      ring
