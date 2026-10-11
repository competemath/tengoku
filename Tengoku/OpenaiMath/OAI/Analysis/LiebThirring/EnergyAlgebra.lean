import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.SobolevProjection

namespace OAI

universe u171 u172 u173 u174 u175 u176 u177 u178

noncomputable section
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

@[simp] lemma val_sub (u v : C1L2) (x : ℝ) : (u-v).val x = u.val x-v.val x := rfl
@[simp] lemma grad_sub (u v : C1L2) (x : ℝ) : (u-v).grad x = u.grad x-v.grad x := rfl

lemma energy_add_left {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (u v w : C1L2) (hw : HasCompactSupport w.val) :
    energy W (u+v) w = energy W u w+energy W v w := by
  simp only [energy,grad_add,val_add,add_mul,mul_add]
  rw [integral_add (u.integrable_grad_mul w) (v.integrable_grad_mul w),
    integral_add (integrable_potential hW u w hw) (integrable_potential hW v w hw)]
  ring

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
