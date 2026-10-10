import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.AffineBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace IndependentProducts
namespace FiniteHead

end FiniteHead

lemma gaussianSquareLaw_memLp : MemLp (fun w : ℝ => w) 2 gaussianSquareLaw := by
  unfold gaussianSquareLaw
  exact (memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr gaussian_square_memLp

lemma gaussianSquareLaw_mean : (∫ w : ℝ, w ∂gaussianSquareLaw) = 1 := by
  rw [gaussianSquareLaw, integral_map (by fun_prop) (by fun_prop)]
  exact gaussian_integral_sq

lemma gaussianSquareLaw_second : (∫ w : ℝ, w ^ 2 ∂gaussianSquareLaw) = 3 := by
  rw [gaussianSquareLaw, integral_map (by fun_prop) (by fun_prop)]
  simpa only [← pow_mul, Nat.reduceMul] using gaussian_integral_fourth

end IndependentProducts

namespace IndependentProducts

end IndependentProducts

end

end OAI
