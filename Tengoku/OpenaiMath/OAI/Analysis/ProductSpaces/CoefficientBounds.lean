import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.RandomSigns

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uΩ uι

namespace IndependentProducts
section CoefficientBound
variable {ι : Type uι} [Fintype ι]

lemma memLp_euclidSize {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (fun ω => euclidSize (fun i => X i ω)) 2 P := by
  apply (memLp_finsetSum _ (fun i _ => (hX i).norm)).mono'
  · unfold euclidSize
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    have ha := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hX i).aestronglyMeasurable.pow 2)
    convert ha using 1
    ext ω
    simp
  · filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (euclidSize_nonneg _)] using
      euclidSize_le_sum_abs (fun i => X i ω)

lemma integral_euclidSize_mul_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun w : ℝ => w) 2 μ) (a : ι → ℝ) :
    (∫ w : ι → ℝ, euclidSize (fun i => w i * a i) ∂Measure.pi (fun _ : ι => μ)) ≤
      Real.sqrt (∫ w : ℝ, w ^ 2 ∂μ) * euclidSize a := by
  have hi : ∀ i, MemLp (fun w : ι → ℝ => w i * a i) 2 (Measure.pi (fun _ : ι => μ)) :=
    fun i => (hμ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).mul_const _
  have h := integral_abs_le_sqrt_sq (memLp_euclidSize _ hi)
  simp_rw [abs_of_nonneg (euclidSize_nonneg _), euclidSize_sq, mul_pow] at h
  have he : (∫ w : ι → ℝ, ∑ i, w i ^ 2 * a i ^ 2 ∂Measure.pi (fun _ : ι => μ)) =
      (∫ w : ℝ, w ^ 2 ∂μ) * ∑ i, a i ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => by
      exact ((hμ.comp_measurePreserving (measurePreserving_eval (fun _ : ι => μ) i)).integrable_sq).mul_const _)]
    simp only [integral_mul_const]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simpa using (measurePreserving_eval (fun _ : ι => μ) i).hasLaw.integral_comp
      (f := fun w : ℝ => w ^ 2) (by fun_prop)
  rw [he, Real.sqrt_mul (integral_nonneg (fun w : ℝ => sq_nonneg w))] at h
  exact h

end CoefficientBound
end IndependentProducts

namespace IndependentProducts
section SignedFirstMoment
variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]

end SignedFirstMoment
end IndependentProducts

end

end OAI
