import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
import Tengoku.Seed.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differentiating convolution against a bounded kernel

A bounded continuous kernel with bounded continuous derivative can be
differentiated under convolution with an arbitrary integrable scalar function.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GeometricBrascampLieb

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure E}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [NormedSpace ℝ E] [CompleteSpace G] in
/--
@isnad1 id=integrab.3h7v.s7.fb1b8702b2bb from=translated src=- shape=1d700bd4 vocab=29d1d5bc
-/
theorem integrable_smul_bounded_kernel {f : E → ℝ} (hf : Integrable f μ)
    {g : E → G} (hg : Continuous g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) (x : E) :
    Integrable (fun z => f z • g (x - z)) μ := by
  apply (hf.norm.mul_const C).mono'
    (hf.aestronglyMeasurable.smul (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖f z • g (x-z)‖ ≤ ‖f z‖ * C
    simpa only [norm_smul] using mul_le_mul_of_nonneg_left (hC (x-z)) (norm_nonneg (f z))

omit [CompleteSpace G] in
/--
@isnad1 id=hasfderi.6h9v.s10.3f8a3071f8ee from=translated src=- shape=e402d326 vocab=c9b6df0e
-/
theorem hasFDerivAt_convolution_of_bounded_kernel {f : E → ℝ} (hf : Integrable f μ)
    {g : E → G} {g' : E → E →L[ℝ] G}
    (hg : Continuous g) (hg' : Continuous g')
    (hd : ∀ y, HasFDerivAt g (g' y) y)
    {C C' : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) (hC' : ∀ y, ‖g' y‖ ≤ C') (x : E) :
    HasFDerivAt (fun y => ∫ z, f z • g (y - z) ∂μ)
      (∫ z, f z • g' (x - z) ∂μ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y z => f z • g' (y-z)) (s := univ) (bound := fun z => ‖f z‖ * C')
    (Filter.univ_mem)
  · exact Eventually.of_forall fun y =>
      (integrable_smul_bounded_kernel hf hg hC y).aestronglyMeasurable
  · exact integrable_smul_bounded_kernel hf hg hC x
  · exact (integrable_smul_bounded_kernel hf hg' hC' x).aestronglyMeasurable
  · exact Eventually.of_forall fun z y _ => by
      simpa only [norm_smul] using mul_le_mul_of_nonneg_left (hC' (y-z)) (norm_nonneg (f z))
  · exact hf.norm.mul_const C'
  · exact Eventually.of_forall fun z y _ => by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using
        ((hd (y-z)).comp y ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const z)).fun_const_smul (f z)

end GeometricBrascampLieb
