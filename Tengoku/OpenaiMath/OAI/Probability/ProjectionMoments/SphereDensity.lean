import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Frames

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma linearEquiv_preserves_ac {m : ℕ} (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    {μ : Measure (Fin m → ℝ)} (hμ : μ ≪ volume) : μ.map T ≪ volume := by
  exact (T.toHomeomorph.toMeasurableEquiv.measurableEmbedding.absolutelyContinuous_map hμ).trans
    (Measure.LinearMap.quasiMeasurePreserving volume T.toLinearEquiv.toLinearMap
      (LinearEquiv.isUnit_det' T.toLinearEquiv).ne_zero).absolutelyContinuous

end ProjectionMoments
end

end

end OAI
