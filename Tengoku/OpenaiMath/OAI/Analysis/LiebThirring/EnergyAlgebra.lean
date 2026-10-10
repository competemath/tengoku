import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.SobolevProjection

namespace OAI

universe u171 u172 u173 u174 u175 u176 u177 u178

noncomputable section
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology

@[simp] lemma val_sub (u v : C1L2) (x : ℝ) : (u-v).val x = u.val x-v.val x := rfl
@[simp] lemma grad_sub (u v : C1L2) (x : ℝ) : (u-v).grad x = u.grad x-v.grad x := rfl

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
