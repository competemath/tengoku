import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.ResidualBounds

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

namespace GaussianPropeller.Reduction

open scoped RealInnerProductSpace

lemma sqrt_value_lower {C : ℝ} (hC : 9/(8*Real.pi) < C) :
    3/(2*Real.sqrt (2*Real.pi)) < Real.sqrt C := by
  have hCp : 0 < C := (by positivity : (0:ℝ) < 9/(8*Real.pi)).trans hC
  have hs : 0 < Real.sqrt (2*Real.pi) := by positivity
  have hs2 : (Real.sqrt (2*Real.pi))^2 = 2*Real.pi := Real.sq_sqrt (by positivity)
  have hrel : (3/(2*Real.sqrt (2*Real.pi)))^2 = 9/(8*Real.pi) := by
    rw [div_pow, mul_pow, hs2]
    ring
  have ht2 := Real.sq_sqrt hCp.le
  have hn : 0 ≤ 3/(2*Real.sqrt (2*Real.pi)) := by positivity
  nlinarith only [hrel,hC,ht2,Real.sqrt_nonneg C]

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem sum_cell_probability {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i, (gaussian d).real (A i) = 1 := by
  let : IsProbabilityMeasure (gaussian d) := by unfold gaussian; infer_instance
  have hsum := integral_congr_ae (sum_indicator_eq hA (fun _ => (1:ℝ)))
  rw [integral_finsetSum] at hsum
  · simpa only [integral_indicator_const (1:ℝ) (hA.1 _), smul_eq_mul, mul_one,
      integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hsum
  · intro i _
    exact (integrable_const (1:ℝ)).indicator (hA.1 i)

omit [NeZero k] in
theorem sum_active_probability {A : Fin k → Set (Space d)} (hA : IsPartition A) :
    ∑ i : activeLabels A, (gaussian d).real (A i) = 1 := by
  classical
  rw [Finset.sum_coe_sort (activeLabels A) (fun i => (gaussian d).real (A i))]
  have he : ∑ i ∈ activeLabels A, (gaussian d).real (A i) = ∑ i, (gaussian d).real (A i) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : gaussian d (A i) = 0 := by simpa only [mem_activeLabels, not_not] using hi
    simp [measureReal_def,hz]
  rw [he,sum_cell_probability hA]

omit [NeZero k] in
theorem sum_active_norm_sq (A : Fin k → Set (Space d)) :
    ∑ i : activeLabels A, ‖centroid (A i)‖^2 = value A := by
  classical
  rw [Finset.sum_coe_sort (activeLabels A) (fun i => ‖centroid (A i)‖^2)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : gaussian d (A i) = 0 := by simpa only [mem_activeLabels, not_not] using hi
  simp [centroid_eq_zero_of_null hz]

omit [NeZero k] in
theorem sum_active_radius_sq (A : Fin k → Set (Space d)) (hpos : 0 < value A) :
    ∑ i : activeLabels A, (‖centroid (A i)‖/Real.sqrt (value A))^2 = 1 := by
  simp only [div_pow, Real.sq_sqrt hpos.le, ← Finset.sum_div, sum_active_norm_sq]
  exact div_self hpos.ne'

end GaussianPropeller.Reduction

end OAI
