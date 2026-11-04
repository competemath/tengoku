import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.KernelEstimate
import Tengoku.Seed.MeasureTheory.Integral.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Probability mixtures of the entropy-curvature kernels

A compactly supported law on positive scales is represented as a probability
measure on the subtype `Icc a b`, where `a > 0`. Every compact subset of the
positive real numbers is contained in such an interval; the later simplex
construction can supply its tilted law directly on this subtype.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace EntropyConstrainedMissingMass
namespace Curvature

/-- Scaling the mixed integral to the unit-mean kernel.-/
theorem mixed_kernel_scaling (c v : ℝ) (hc : 0 < c) (hv : 0 < v) :
    (∫ s in Ioi (0 : ℝ), (s - c) ^ 2 * kernel c s * kernel v s) = c * J (v / c) := by
  have heq : (∫ s in Ioi (0 : ℝ), (c * s - c) ^ 2 * kernel c (c * s) * kernel v (c * s)) =
      J (v / c) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    have hs0 : 0 < s := mem_Ioi.mp hs
    unfold kernel
    have hsc : c * s + c ≠ 0 := by positivity
    have hvc : c * s + v ≠ 0 := by positivity
    have hs1 : s + 1 ≠ 0 := by linarith [mem_Ioi.mp hs]
    have hsq : s + v / c ≠ 0 := by positivity
    field_simp
  have h := integral_comp_mul_left_Ioi'
    (fun s : ℝ => (s - c) ^ 2 * kernel c s * kernel v s) 0 hc
  simpa only [mul_zero, smul_eq_mul, heq] using h.symm

/-- Uniform upper control of a kernel whose scale belongs to a positive interval.-/
theorem kernel_parameter_bound (a b v s : ℝ) (ha : 0 < a)
    (hv : v ∈ Icc a b) (hs : 0 ≤ s) :
    0 ≤ kernel v s ∧ kernel v s ≤ 2 * b ^ 2 * (1 / (s + a) ^ 3) := by
  have hvpos : 0 < v := lt_of_lt_of_le ha hv.1
  have hb : 0 < b := lt_of_lt_of_le hvpos hv.2
  unfold kernel
  constructor
  · positivity
  · simp only [one_div]
    rw [← div_eq_mul_inv]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hvpos) hv.2 2) (by norm_num))
      (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith [hv.1]) 3)

/-- Mean scale of a compactly supported probability law.-/
noncomputable def mixtureMean {a b : ℝ} (μ : Measure (Icc a b)) : ℝ :=
  ∫ v, (v : ℝ) ∂μ

/-- The mixture kernel density.-/
noncomputable def mixtureDensity {a b : ℝ} (μ : Measure (Icc a b)) (s : ℝ) : ℝ :=
  ∫ v, kernel (v : ℝ) s ∂μ

section Mixture

variable {a b : ℝ} (μ : Measure (Icc a b)) [IsProbabilityMeasure μ]

private theorem integrable_continuous_parameter {f : Icc a b → ℝ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The mean belongs to the same compact interval as all scales.-/
theorem mixtureMean_mem : mixtureMean μ ∈ Icc a b := by
  have hi : Integrable (fun v : Icc a b => (v : ℝ)) μ :=
    integrable_continuous_parameter μ continuous_subtype_val
  constructor
  · have h := integral_mono (integrable_const a) hi (fun v => v.property.1)
    simpa [mixtureMean] using h
  · have h := integral_mono hi (integrable_const b) (fun v => v.property.2)
    simpa [mixtureMean] using h

/-- Positivity of the mean follows from the positive support interval.-/
theorem mixtureMean_pos (ha : 0 < a) : 0 < mixtureMean μ :=
  lt_of_lt_of_le ha (mixtureMean_mem μ).1

/-- Integrability with respect to the scale law at every nonnegative location.-/
theorem integrable_kernel_parameter (ha : 0 < a) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun v : Icc a b => kernel (v : ℝ) s) μ := by
  apply integrable_continuous_parameter μ
  unfold kernel
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro v
    have hv : 0 < (v : ℝ) := lt_of_lt_of_le ha v.property.1
    positivity

/-- The mixture inherits a uniform positive-integrable kernel bound.-/
theorem mixtureDensity_bound (ha : 0 < a) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ mixtureDensity μ s ∧
      mixtureDensity μ s ≤ 2 * b ^ 2 * (1 / (s + a) ^ 3) := by
  constructor
  · exact integral_nonneg (fun v => (kernel_parameter_bound a b v s ha v.property hs).1)
  · have h := integral_mono (integrable_kernel_parameter μ ha s hs)
      (integrable_const (2 * b ^ 2 * (1 / (s + a) ^ 3)))
      (fun v => (kernel_parameter_bound a b v s ha v.property hs).2)
    simpa [mixtureDensity] using h

/-- Global measurability of the mixed density, including outside its integration domain.-/
theorem stronglyMeasurable_mixtureDensity : StronglyMeasurable (mixtureDensity μ) := by
  have h : Measurable (fun p : ℝ × Icc a b => kernel (p.2 : ℝ) p.1) := by
    unfold kernel
    fun_prop
  exact h.stronglyMeasurable.integral_prod_right'

private theorem quadratic_product_bound (a b c s G H : ℝ) (ha : 0 < a) (hs : 0 ≤ s)
    (hG : 0 ≤ G ∧ G ≤ 2 * b ^ 2 * (1 / (s + a) ^ 3))
    (hH : 0 ≤ H ∧ H ≤ 2 * b ^ 2 * (1 / (s + a) ^ 3)) :
    ‖(s - c) ^ 2 * G * H‖ ≤ 4 * b ^ 4 * ((s - c) ^ 2 / (D a a a s) ^ 2) := by
  have hB : 0 ≤ 2 * b ^ 2 * (1 / (s + a) ^ 3) := by positivity
  have hh := mul_le_mul hG.2 hH.2 hH.1 hB
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hG.1) hH.1)]
  calc
    (s - c) ^ 2 * G * H = (s - c) ^ 2 * (G * H) := by ring
    _ ≤ (s - c) ^ 2 * ((2 * b ^ 2 * (1 / (s + a) ^ 3)) *
      (2 * b ^ 2 * (1 / (s + a) ^ 3))) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = 4 * b ^ 4 * ((s - c) ^ 2 / (D a a a s) ^ 2) := by
      rw [D_uniform]
      have hsa : s + a ≠ 0 := by positivity
      field_simp
      ring

/-- The mixed quadratic kernel is integrable on location × scale, which justifies Fubini.-/
theorem integrable_mixed_kernel_prod (ha : 0 < a) (c : ℝ) (hc : c ∈ Icc a b) :
    Integrable (fun p : ℝ × Icc a b => (p.1 - c) ^ 2 * kernel c p.1 * kernel p.2 p.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
  have hi : Integrable (fun s : ℝ => 4 * b ^ 4 * ((s - c) ^ 2 / (D a a a s) ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_curvature_numerator a a a c ha ha ha).const_mul (4 * b ^ 4)
  have hm : Measurable (fun p : ℝ × Icc a b =>
      (p.1 - c) ^ 2 * kernel c p.1 * kernel p.2 p.1) := by
    unfold kernel
    fun_prop
  refine (hi.comp_fst μ).mono' hm.aestronglyMeasurable ?_
  have hs : ∀ᵐ p : ℝ × Icc a b ∂((volume.restrict (Ioi (0 : ℝ))).prod μ), 0 < p.1 := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact Filter.Eventually.of_forall (fun _ => hs)
  filter_upwards [hs] with p hp
  exact quadratic_product_bound a b c p.1 _ _ ha (le_of_lt hp)
    (kernel_parameter_bound a b c p.1 ha hc (le_of_lt hp))
    (kernel_parameter_bound a b p.2 p.1 ha p.2.property (le_of_lt hp))

/-- Integrability of the mixed quadratic expression after averaging the scale.-/
theorem integrableOn_mixed_mixture (ha : 0 < a) (c : ℝ) (hc : c ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => (s - c) ^ 2 * kernel c s * mixtureDensity μ s)
      (Ioi (0 : ℝ)) := by
  have hi := (integrable_mixed_kernel_prod μ ha c hc).integral_prod_left
  simpa only [IntegrableOn, integral_const_mul, mixtureDensity] using hi

/-- The quadratic mixture itself is integrable by a uniform inverse-power bound.-/
theorem integrableOn_mixture_square (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun s : ℝ => (s - c) ^ 2 * (mixtureDensity μ s) ^ 2)
      (Ioi (0 : ℝ)) := by
  have hi := (integrableOn_curvature_numerator a a a c ha ha ha).const_mul (4 * b ^ 4)
  have hm : StronglyMeasurable (fun s : ℝ => (s - c) ^ 2 * (mixtureDensity μ s) ^ 2) := by
    exact ((measurable_id.sub_const c).pow_const 2).stronglyMeasurable.mul
      ((stronglyMeasurable_mixtureDensity μ).pow 2)
  refine hi.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have h := quadratic_product_bound a b c s _ _ ha (le_of_lt hs)
    (mixtureDensity_bound μ ha s (le_of_lt hs)) (mixtureDensity_bound μ ha s (le_of_lt hs))
  simpa only [pow_two, mul_assoc] using h

/-- Fubini identifies the averaged mixed-kernel integral with the mixture cross term.-/
theorem integral_mixed_mixture_eq (ha : 0 < a) (c : ℝ) (hc : c ∈ Icc a b) :
    (∫ s in Ioi (0 : ℝ), (s - c) ^ 2 * kernel c s * mixtureDensity μ s) =
      ∫ v : Icc a b, (∫ s in Ioi (0 : ℝ), (s - c) ^ 2 * kernel c s * kernel v s) ∂μ := by
  have h := integral_integral_swap
    (f := fun s (v : Icc a b) => (s - c) ^ 2 * kernel c s * kernel v s)
    (integrable_mixed_kernel_prod μ ha c hc)
  simpa only [integral_const_mul, mixtureDensity] using h

/-- The dispersion term in the mixture estimate.-/
noncomputable def mixtureDispersion : ℝ :=
  ∫ v : Icc a b, ((v : ℝ) - mixtureMean μ) ^ 2 / ((v : ℝ) + mixtureMean μ) ∂μ

/-- The squared reference kernel has the exact quadratic integral used in the expansion.-/
theorem integral_kernel_square (c : ℝ) (hc : 0 < c) :
    (∫ s in Ioi (0 : ℝ), (s - c) ^ 2 * (kernel c s) ^ 2) = 8 * c / 15 := by
  have heq : (fun s : ℝ => (s - c) ^ 2 * (kernel c s) ^ 2) =
      (fun s : ℝ => (s - c) ^ 2 * kernel c s * kernel c s) := by funext s; ring
  rw [heq, mixed_kernel_scaling c c hc hc, div_self (ne_of_gt hc), J_one]
  ring

end Mixture
end Curvature
end EntropyConstrainedMissingMass
