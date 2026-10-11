import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.CapDomination

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fractionalBlock_mass_identity {J : Type*} [Fintype J] {k : ℕ}
    (Q : J → (Fin k → E) × Label k → ℝ≥0∞) (hQ : ∀ j, Measurable (Q j))
    (f : J → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j))
    (μ : Measure E) [SFinite μ] {S : Set E} (hS : MeasurableSet S) :
    (∫⁻ s in S, fractionalBlock Q f s ∂μ) =
      ∑ j, ∫⁻ s, capKernelValue (Q j) s ∂(μ.withDensity (f j)).restrict S := by
  have he (s : E) : fractionalBlock Q f s = ∑ j, f j s * capKernelValue (Q j) s := by
    unfold fractionalBlock capKernelValue
    rw [lintegral_finsetSum _ (fun j _ => by simp only [rowMap_apply]; fun_prop)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [lintegral_mul_const _ (by simp only [rowMap_apply]; fun_prop)]
    exact mul_comm _ _
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun j _ => show Measurable (fun s => f j s * capKernelValue (Q j) s) from
    (hf j).mul (measurable_capKernelValue (hQ j)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [restrict_withDensity hS]
  exact (lintegral_withDensity_eq_lintegral_mul _ (hf j) (measurable_capKernelValue (hQ j))).symm

end ProjectionMoments

end

end OAI
