module

public import Tengoku.AtPalomar.Paper.DoobKernel
public import Tengoku.Seed.Probability.Kernel.WithDensity
public import Tengoku.Seed.Probability.Kernel.Composition.Comp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Probability kernels for the post-overlap state

This file constructs the normalized cosh transform as an actual Markov
kernel. Identifying the resulting transition law with a stochastic
differential equation is a separate stochastic-calculus problem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Paper

/-- The Gaussian transition kernel at variance `v`.-/
def gaussianStateKernel (v : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := gaussianReal x v
  measurable' := measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)

/--
@isnad1 id=eq.0h2v.s4.687d12bb103b from=translated src=- shape=f93c5ac9 vocab=5d14f0c5
-/
@[simp] theorem gaussianStateKernel_apply (v : ℝ≥0) (x : ℝ) :
    gaussianStateKernel v x = gaussianReal x v := rfl

/--
@isnad1 id=ismarkov.0h1v.s3.239210716c26 from=translated src=- shape=f614ea99 vocab=38aeedb0
-/
instance gaussianStateKernel_isMarkov (v : ℝ≥0) : IsMarkovKernel (gaussianStateKernel v) where
  isProbabilityMeasure x := inferInstanceAs (IsProbabilityMeasure (gaussianReal x v))

/-- Gaussian transition kernels satisfy the Chapman--Kolmogorov equation.
@isnad1 id=eq.0h2v.s5.e89dab3c4fb1 from=translated src=- shape=b1d5b414 vocab=0cd54390
-/
theorem gaussianStateKernel_comp (u v : ℝ≥0) :
    gaussianStateKernel v ∘ₖ gaussianStateKernel u = gaussianStateKernel (u + v) := by
  refine Kernel.ext_fun fun x f hf => ?_
  rw [Kernel.lintegral_comp _ _ _ hf]
  simp only [gaussianStateKernel_apply]
  have hshift (y : ℝ) :
      (∫⁻ z, f z ∂gaussianReal y v) =
        ∫⁻ z, f (y + z) ∂gaussianReal 0 v := by
    have hm : (gaussianReal 0 v).map (fun z => y + z) = gaussianReal y v := by
      simpa using (gaussianReal_map_const_add (μ := 0) (v := v) y)
    rw [← hm, lintegral_map hf (by fun_prop)]
  simp_rw [hshift]
  have hc : gaussianReal x u ∗ gaussianReal 0 v = gaussianReal x (u + v) := by
    simpa using (gaussianReal_conv_gaussianReal (m₁ := x) (m₂ := 0) (v₁ := u) (v₂ := v))
  rw [← hc, Measure.lintegral_conv hf]

/--
@isnad1 id=eq.0h0v.s4.09ddc5bfc975 from=translated src=- shape=6b9a3452 vocab=dc312732
-/
@[simp] theorem gaussianStateKernel_zero : gaussianStateKernel 0 = Kernel.id := by
  ext x
  simp [gaussianReal_zero_var, Kernel.id_apply]

/-- The positive Radon--Nikodym multiplier of the cosh transform.-/
def coshStateDensity (v : ℝ≥0) (x y : ℝ) : ℝ :=
  Real.exp (-(v : ℝ) / 2) / Real.cosh x * Real.cosh y

/--
@isnad1 id=lt.0h3v.s4.aba6bca619e3 from=translated src=- shape=877de13a vocab=b2fdfa66
-/
theorem coshStateDensity_pos (v : ℝ≥0) (x y : ℝ) :
    0 < coshStateDensity v x y :=
  mul_pos (div_pos (Real.exp_pos _) (Real.cosh_pos _)) (Real.cosh_pos _)

/-- Completing the square gives the exponential tilt of a Gaussian density.
@isnad1 id=eq.1h4v.s7.7d9548e64033 from=translated src=- shape=6a329c16 vocab=b511f87e
-/
theorem gaussianPDFReal_exponential_tilt (x c y : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Real.exp (c * y - c * x - c ^ 2 * (v : ℝ) / 2) * gaussianPDFReal x v y =
      gaussianPDFReal (x + c * (v : ℝ)) v y := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hexp : c * y - c * x - c ^ 2 * (v : ℝ) / 2 +
      (-(y - x) ^ 2 / (2 * (v : ℝ))) =
      -(y - (x + c * (v : ℝ))) ^ 2 / (2 * (v : ℝ)) := by
    field_simp
    ring
  unfold gaussianPDFReal
  calc
    Real.exp (c * y - c * x - c ^ 2 * (v : ℝ) / 2) *
        ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(y - x) ^ 2 / (2 * (v : ℝ)))) =
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
        Real.exp (c * y - c * x - c ^ 2 * (v : ℝ) / 2 +
          (-(y - x) ^ 2 / (2 * (v : ℝ)))) := by
            rw [Real.exp_add]
            ring
    _ = _ := by rw [hexp]

/-- Posterior weight of the positive unit drift.-/
def positiveDriftWeight (x : ℝ) : ℝ := Real.exp x / (2 * Real.cosh x)

/-- Posterior weight of the negative unit drift.-/
def negativeDriftWeight (x : ℝ) : ℝ := Real.exp (-x) / (2 * Real.cosh x)

/--
@isnad1 id=and.0h1v.s4.75c26acda739 from=translated src=- shape=00bd4da5 vocab=b0db054a
-/
theorem driftWeights_nonneg (x : ℝ) :
    0 ≤ positiveDriftWeight x ∧ 0 ≤ negativeDriftWeight x := by
  simp only [positiveDriftWeight, negativeDriftWeight]
  constructor <;> positivity

/--
@isnad1 id=eq.0h1v.s4.def2273bc5fc from=translated src=- shape=72c058d5 vocab=7d30a03f
-/
theorem driftWeights_sum (x : ℝ) : positiveDriftWeight x + negativeDriftWeight x = 1 := by
  unfold positiveDriftWeight negativeDriftWeight
  rw [← add_div, Real.cosh_eq]
  field_simp

/-- The cosh transition density is the explicit mixture of the two
constant-drift Gaussian densities.
@isnad1 id=eq.1h3v.s6.bb7d230be3ab from=translated src=- shape=3b3f37e5 vocab=a857ba9e
-/
theorem coshStateDensity_gaussian_mixture (v : ℝ≥0) (hv : v ≠ 0) (x y : ℝ) :
    coshStateDensity v x y * gaussianPDFReal x v y =
      positiveDriftWeight x * gaussianPDFReal (x + (v : ℝ)) v y +
        negativeDriftWeight x * gaussianPDFReal (x - (v : ℝ)) v y := by
  have hp : Real.exp (y - x - (v : ℝ) / 2) * gaussianPDFReal x v y =
      gaussianPDFReal (x + (v : ℝ)) v y := by
    simpa using gaussianPDFReal_exponential_tilt x 1 y v hv
  have hn : Real.exp (-y + x - (v : ℝ) / 2) * gaussianPDFReal x v y =
      gaussianPDFReal (x - (v : ℝ)) v y := by
    simpa [sub_eq_add_neg] using gaussianPDFReal_exponential_tilt x (-1) y v hv
  have heP : Real.exp x * Real.exp (y - x - (v : ℝ) / 2) =
      Real.exp (-(v : ℝ) / 2) * Real.exp y := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have heN : Real.exp (-x) * Real.exp (-y + x - (v : ℝ) / 2) =
      Real.exp (-(v : ℝ) / 2) * Real.exp (-y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hRP : positiveDriftWeight x * gaussianPDFReal (x + (v : ℝ)) v y =
      (Real.exp (-(v : ℝ) / 2) * Real.exp y * gaussianPDFReal x v y) /
        (2 * Real.cosh x) := by
    rw [positiveDriftWeight, ← hp, div_mul_eq_mul_div, ← mul_assoc, heP]
  have hRN : negativeDriftWeight x * gaussianPDFReal (x - (v : ℝ)) v y =
      (Real.exp (-(v : ℝ) / 2) * Real.exp (-y) * gaussianPDFReal x v y) /
        (2 * Real.cosh x) := by
    rw [negativeDriftWeight, ← hn, div_mul_eq_mul_div, ← mul_assoc, heN]
  rw [hRP, hRN, ← add_div]
  unfold coshStateDensity
  rw [Real.cosh_eq y]
  have hx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp

/--
@isnad1 id=measurab.0h1v.s4.20bd76944835 from=translated src=- shape=7ccd5b43 vocab=f1d46b87
-/
theorem measurable_coshStateDensity (v : ℝ≥0) :
    Measurable (Function.uncurry (coshStateDensity v)) := by
  unfold coshStateDensity Function.uncurry
  fun_prop

/--
@isnad1 id=integrab.0h2v.s5.e3cb8002b27b from=translated src=- shape=a0d88c3a vocab=94f6e2f2
-/
theorem integrable_coshStateDensity (v : ℝ≥0) (x : ℝ) :
    Integrable (coshStateDensity v x) (gaussianReal x v) :=
  (integrable_cosh_gaussianReal x v).const_mul _

/--
@isnad1 id=eq.0h2v.s5.4e4b69d79fa2 from=translated src=- shape=9b963a3e vocab=e73704c1
-/
theorem integral_coshStateDensity (v : ℝ≥0) (x : ℝ) :
    (∫ y, coshStateDensity v x y ∂gaussianReal x v) = 1 := by
  simpa [coshStateDensity, integral_const_mul, doobOperator] using doobOperator_one v x

/-- The density multipliers cancel at the intermediate state.
@isnad1 id=eq.0h5v.s5.083415fc418e from=translated src=- shape=2e1221fe vocab=5dd1e132
-/
theorem coshStateDensity_chain (u v : ℝ≥0) (x y z : ℝ) :
    coshStateDensity u x y * coshStateDensity v y z = coshStateDensity (u + v) x z := by
  unfold coshStateDensity
  simp only [NNReal.coe_add]
  have hy : Real.cosh y ≠ 0 := (Real.cosh_pos y).ne'
  have hx : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

/-- The actual normalized transition kernel corresponding to `doobOperator`.-/
def coshStateKernel (v : ℝ≥0) : Kernel ℝ ℝ :=
  Kernel.withDensity (gaussianStateKernel v)
    (fun x y => ENNReal.ofReal (coshStateDensity v x y))

/--
@isnad1 id=eq.0h2v.s5.73aefa2a5bcb from=translated src=- shape=fef0fb89 vocab=4fc55f1d
-/
@[simp] theorem coshStateKernel_apply (v : ℝ≥0) (x : ℝ) :
    coshStateKernel v x = (gaussianReal x v).withDensity
      (fun y => ENNReal.ofReal (coshStateDensity v x y)) := by
  exact Kernel.withDensity_apply _ (measurable_coshStateDensity v).ennreal_ofReal x

/--
@isnad1 id=eq.1h3v.s6.3a5d92c70fd7 from=translated src=- shape=135f342a vocab=83fa2a12
-/
theorem lintegral_coshStateKernel (v : ℝ≥0) (x : ℝ) (ψ : ℝ → ℝ≥0∞)
    (hψ : Measurable ψ) :
    (∫⁻ y, ψ y ∂coshStateKernel v x) =
      ∫⁻ y, ENNReal.ofReal (coshStateDensity v x y) * ψ y ∂gaussianReal x v := by
  exact Kernel.lintegral_withDensity _ (measurable_coshStateDensity v).ennreal_ofReal x hψ

/-- Chapman--Kolmogorov for the actual cosh state probability kernels.
@isnad1 id=eq.0h2v.s5.5086e9c53fad from=translated src=- shape=b1d5b414 vocab=209a83ca
-/
theorem coshStateKernel_comp (u v : ℝ≥0) :
    coshStateKernel v ∘ₖ coshStateKernel u = coshStateKernel (u + v) := by
  refine Kernel.ext_fun fun x f hf => ?_
  rw [Kernel.lintegral_comp _ _ _ hf,
    lintegral_coshStateKernel u x _ (Measurable.lintegral_kernel (κ := coshStateKernel v) hf),
    lintegral_coshStateKernel (u + v) x f hf]
  simp_rw [lintegral_coshStateKernel v _ f hf]
  have hcollapse (y : ℝ) :
      ENNReal.ofReal (coshStateDensity u x y) *
        (∫⁻ z, ENNReal.ofReal (coshStateDensity v y z) * f z ∂gaussianReal y v) =
      ∫⁻ z, ENNReal.ofReal (coshStateDensity (u + v) x z) * f z ∂gaussianReal y v := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    rw [← mul_assoc, ← ENNReal.ofReal_mul (coshStateDensity_pos u x y).le,
      coshStateDensity_chain]
  simp_rw [hcollapse]
  have hm : Measurable (fun z => ENNReal.ofReal (coshStateDensity (u + v) x z) * f z) :=
    ((measurable_coshStateDensity (u + v)).of_uncurry_left.ennreal_ofReal).mul hf
  have heq := congrArg
    (fun K : Kernel ℝ ℝ => ∫⁻ z, ENNReal.ofReal (coshStateDensity (u + v) x z) * f z ∂K x)
    (gaussianStateKernel_comp u v)
  rw [Kernel.lintegral_comp _ _ _ hm] at heq
  exact heq

/--
@isnad1 id=eq.0h0v.s4.86896c43dc9e from=translated src=- shape=6b9a3452 vocab=2d7338d6
-/
@[simp] theorem coshStateKernel_zero : coshStateKernel 0 = Kernel.id := by
  refine Kernel.ext_fun fun x f hf => ?_
  rw [lintegral_coshStateKernel 0 x f hf]
  simp [coshStateDensity, gaussianReal_zero_var, (Real.cosh_pos x).ne',
    Kernel.id_apply, lintegral_dirac' x hf]

/-- The kernel integral is exactly the analytic operator, for every real
test function; both sides use the same totalized Bochner integral.
@isnad1 id=eq.0h3v.s5.de06123dcfaf from=translated src=- shape=17d4f44e vocab=dbb013c0
-/
theorem integral_coshStateKernel (v : ℝ≥0) (x : ℝ) (ψ : ℝ → ℝ) :
    (∫ y, ψ y ∂coshStateKernel v x) = doobOperator v ψ x := by
  rw [coshStateKernel_apply,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_coshStateDensity v).of_uncurry_left.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (coshStateDensity_pos v x _).le, smul_eq_mul]
  simp [coshStateDensity, doobOperator, mul_assoc, integral_const_mul]

/-- The state transition probability is an explicit mixture of Gaussian
increments with drift `+1` and drift `-1`, including variance zero.
@isnad1 id=eq.0h2v.s7.3146d84e3ec7 from=translated src=- shape=803abb60 vocab=1ff0f088
-/
theorem coshStateKernel_gaussian_mixture (v : ℝ≥0) (x : ℝ) :
    coshStateKernel v x =
      ENNReal.ofReal (positiveDriftWeight x) • gaussianReal (x + (v : ℝ)) v +
        ENNReal.ofReal (negativeDriftWeight x) • gaussianReal (x - (v : ℝ)) v := by
  obtain ⟨hp, hn⟩ := driftWeights_nonneg x
  by_cases hv : v = 0
  · subst v
    simp only [coshStateKernel_zero, Kernel.id_apply, NNReal.coe_zero, add_zero, sub_zero,
      gaussianReal_zero_var]
    rw [← add_smul, ← ENNReal.ofReal_add hp hn, driftWeights_sum]
    simp
  rw [coshStateKernel_apply, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul _ (measurable_gaussianPDF _ _)
      ((measurable_coshStateDensity v).of_uncurry_left.ennreal_ofReal),
    gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_smul _ (measurable_gaussianPDF _ _),
    ← withDensity_smul _ (measurable_gaussianPDF _ _),
    ← withDensity_add_right _ (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards with y
  have h := congrArg ENNReal.ofReal (coshStateDensity_gaussian_mixture v hv x y)
  simpa only [gaussianPDF, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply,
    ENNReal.ofReal_mul (coshStateDensity_pos v x y).le,
    ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hn,
    ENNReal.ofReal_add
      (mul_nonneg hp (gaussianPDFReal_nonneg _ _ _))
      (mul_nonneg hn (gaussianPDFReal_nonneg _ _ _)), mul_comm] using h

end Paper
