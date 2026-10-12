import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.Scalar

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
open OneCell
variable {d:ℕ}

lemma sqrt_threshold {C:ℝ} (hC:9/(8*Real.pi)<C) :
    (3/2:ℝ)*gaussianConst < Real.sqrt C := by
  have hCp:0<C := (by positivity : (0:ℝ)<9/(8*Real.pi)).trans hC
  have hc0:0≤gaussianConst := by unfold gaussianConst; positivity
  have hc2:gaussianConst^2=1/(2*Real.pi) := by
    rw [gaussianConst,inv_pow,Real.sq_sqrt (by positivity),one_div]
  apply (sq_lt_sq₀ (by positivity : 0≤(3/2:ℝ)*gaussianConst) (Real.sqrt_nonneg C)).mp
  rw [mul_pow,hc2,Real.sq_sqrt hCp.le]
  have he : (3/2:ℝ)^2*(1/(2*Real.pi))=9/(8*Real.pi) := by field_simp; ring
  rwa [he]

end GaussianPropeller.Reduction

end OAI
