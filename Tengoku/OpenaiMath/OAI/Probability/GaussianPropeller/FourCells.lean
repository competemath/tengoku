import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.SmallCell

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open FourCertificates ProbabilityBounds
open scoped RealInnerProductSpace
variable {d:ℕ}

lemma triangle_gram (u v w : Space d) (hs:u+v+w=0) :
    let D:=‖u‖^2*‖v‖^2-⟪u,v⟫^2
    D=‖u‖^2*‖w‖^2-⟪u,w⟫^2 ∧ D=‖v‖^2*‖w‖^2-⟪v,w⟫^2 ∧
    4*D=(‖u‖^2+‖v‖^2+‖w‖^2)^2-2*(‖u‖^4+‖v‖^4+‖w‖^4) := by
  have hw:w=-(u+v) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs)
  subst w
  simp only [norm_neg,norm_add_sq_real,inner_neg_right,inner_add_right,real_inner_self_eq_norm_sq,
    real_inner_comm u v]
  constructor
  · ring
  constructor
  · ring
  · have h4:‖u+v‖^4=(‖u‖^2+‖v‖^2+2*⟪u,v⟫)^2 := by rw [show (4:ℕ)=2*2 by rfl,pow_mul,norm_add_sq_real]; ring
    rw [h4]
    ring

lemma residual_fourth_le (x y:Space d) (hx:x≠0) :
    ‖residualVector x y‖^4≤‖y‖^4 := by
  have h:=residual_norm_sq (z:=x) (y:=y) hx
  have hle:‖residualVector x y‖^2≤‖y‖^2 := by nlinarith only [h,mul_nonneg (sq_nonneg (residualCoefficient x y)) (sq_nonneg ‖x‖)]
  have hh: (‖residualVector x y‖^2)^2≤(‖y‖^2)^2 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hle
  simpa only [←pow_mul] using hh

end GaussianPropeller.Reduction

end OAI
