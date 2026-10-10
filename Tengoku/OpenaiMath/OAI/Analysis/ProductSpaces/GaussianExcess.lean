import Tengoku.OpenaiMath.OAI.Analysis.ProductSpaces.GaussianMoments

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι

namespace IndependentProducts
section GaussianScalar
variable {ι : Type uι} [Fintype ι]

lemma integrable_gaussian_quadratic (a : ι → ℝ) (b : ℝ) :
    Integrable (fun x : ι → ℝ => b + ∑ i, a i * x i ^ 2) gaussianVector := by
  apply (integrable_const b).add
  apply integrable_finsetSum
  intro i _
  exact ((gaussian_square_memLp.comp_measurePreserving
    (measurePreserving_eval (fun _ => gaussianReal 0 1) i)).integrable (by norm_num)).const_mul _

lemma gaussian_quadratic_difference (a : ι → ℝ) (b : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    ((b + ∑ i, a i * z.1 i ^ 2) - (b + ∑ i, a i * z.2 i ^ 2)) / 2 =
      ∑ i, a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i := by
  have he : ∀ i, a i * z.1 i ^ 2 - a i * z.2 i ^ 2 =
      2 * (a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i) := by
    intro i
    rw [← mul_sub, gaussian_polarization (z.1 i, z.2 i)]
    dsimp [gaussianVectorRotate]
    ring
  have hh : (∑ i, a i * z.1 i ^ 2) - (∑ i, a i * z.2 i ^ 2) =
      2 * ∑ i, a i * (gaussianVectorRotate z).1 i * (gaussianVectorRotate z).2 i := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [he, ← Finset.mul_sum]
  linarith

end GaussianScalar
end IndependentProducts

end

end OAI
