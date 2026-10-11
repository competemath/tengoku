import Tengoku.OpenaiMath.OAI.Probability.GaussianReplacement.Hybrid

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

lemma shannonEntropy_le_log_card {W : Type*} [Fintype W] [MeasurableSpace W]
    [MeasurableSingletonClass W] (π : Measure W) [IsProbabilityMeasure π] :
    (shannonEntropy π).toReal ≤ Real.log (Fintype.card W) := by
  let : Nonempty W := nonempty_of_isProbabilityMeasure π
  let Q := (PMF.uniformOfFintype W).toMeasure
  have hQ : ∀ w, Q {w} = (Fintype.card W:ℝ≥0∞)⁻¹ := by
    intro w
    change (PMF.uniformOfFintype W).toMeasure {w} = _
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w),PMF.uniformOfFintype_apply]
  have hq0 : (Fintype.card W:ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hPQ : π ≪ Q := countable_ac_of_atom π Q (by intro w hw; exact (hq0 ((hQ w).symm.trans hw)).elim)
  obtain ⟨_,hb⟩ := countable_entropy_le_crossEntropy π Q hPQ (Integrable.of_finite)
  have he : (fun w => -Real.log (Q {w}).toReal) = fun _ : W => Real.log (Fintype.card W) := by
    funext w
    rw [hQ w,ENNReal.toReal_inv,ENNReal.toReal_natCast,Real.log_inv,neg_neg]
  simpa [he] using hb

end CurrentProjection

end

end OAI
