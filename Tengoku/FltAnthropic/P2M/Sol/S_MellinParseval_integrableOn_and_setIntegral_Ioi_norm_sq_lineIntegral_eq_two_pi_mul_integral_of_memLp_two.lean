import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two

set_option autoImplicit false

open MeasureTheory SchwartzMap Real
open scoped FourierTransform ComplexConjugate ContDiff

namespace MellinPlancherel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/--
@isnad1 id=eventual.2h3v.s10.9bafab75a8bb from=translated src=- shape=0e359b2d vocab=a7fdf636
-/
theorem coeFn_fourier_toLp_ae_eq (f : V → F) (hf : Integrable f) (hf2 : MemLp f 2 volume) :
    ((𝓕 (hf2.toLp f) : Lp F 2 (volume : Measure V)) : V → F) =ᵐ[volume] 𝓕 f := by
  set u : Lp F 2 (volume : Measure V) := hf2.toLp f with hu
  set U : Lp F 2 (volume : Measure V) := 𝓕 u with hU
  have hUli : LocallyIntegrable (U : V → F) volume :=
    (Lp.memLp U).locallyIntegrable (by norm_num)
  have hFf_cont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hf
  have hFfli : LocallyIntegrable (𝓕 f) volume := hFf_cont.locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hUli hFfli ?_
  intro g hg hgc
  have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left Complex.ofReal_zero
  have hg' : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  set G : 𝓢(V, ℂ) := hgc'.toSchwartzMap hg' with hG
  have hGcoe : ∀ x, G x = (g x : ℂ) := fun x => rfl

  have h1 : (Lp.toTemperedDistribution U) G = (Lp.toTemperedDistribution u) (𝓕 G) := by
    rw [hU, ← Lp.fourier_toTemperedDistribution_eq u, TemperedDistribution.fourier_apply]
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at h1

  have h2 : ∫ x, (𝓕 G) x • (u : V → F) x = ∫ x, (𝓕 G) x • f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]

  have h3 : ∫ x, (𝓕 (G : V → ℂ)) x • f x = ∫ x, (G : V → ℂ) x • 𝓕 f x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      (μ := (volume : Measure V)) (ν := (volume : Measure V))
      Real.continuous_fourierChar (by exact continuous_inner) G.integrable hf
    rw [flip_innerₗ] at h
    exact h
  have h4 : ∫ x, (G : V → ℂ) x • (U : V → F) x = ∫ x, (G : V → ℂ) x • 𝓕 f x := by
    rw [h1, h2, fourier_coe, h3]
  simp only [hGcoe, Complex.coe_smul] at h4
  exact h4

/--
@isnad1 id=and.2h3v.s8.13d08d20c112 from=translated src=- shape=11b00f49 vocab=bcb4a0dc
-/
theorem memLp_two_fourier_and_integral_norm_sq_eq (f : V → F) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) :
    MemLp (𝓕 f) 2 volume ∧ ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hae := coeFn_fourier_toLp_ae_eq f hf hf2
  set u : Lp F 2 (volume : Measure V) := hf2.toLp f with hu
  set U : Lp F 2 (volume : Measure V) := 𝓕 u with hU
  refine ⟨(Lp.memLp U).ae_eq hae, ?_⟩
  have hinner : inner ℂ U U = inner ℂ u u := by rw [hU]; exact Lp.inner_fourier_eq u u
  rw [L2.inner_def, L2.inner_def] at hinner
  simp_rw [inner_self_eq_norm_sq_to_K] at hinner
  have h5 : ∫ a, ‖(U : V → F) a‖ ^ 2 = ∫ a, ‖(u : V → F) a‖ ^ 2 := by
    have h6 : ((∫ a, ‖(U : V → F) a‖ ^ 2 : ℝ) : ℂ) = ((∫ a, ‖(u : V → F) a‖ ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal]
      push_cast
      exact hinner
    exact_mod_cast h6
  calc ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ a, ‖(U : V → F) a‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        rw [hx]
    _ = ∫ a, ‖(u : V → F) a‖ ^ 2 := h5
    _ = ∫ x, ‖f x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]

/--
@isnad1 id=and.2h3v.s8.763bc9a7f187 from=translated src=- shape=11b00f49 vocab=a13ad0d1
-/
theorem memLp_two_fourierInv_and_integral_norm_sq_eq (f : V → F) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) :
    MemLp (𝓕⁻ f) 2 volume ∧ ∫ ξ, ‖𝓕⁻ f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := memLp_two_fourier_and_integral_norm_sq_eq f hf hf2
  have hfun : 𝓕⁻ f = fun w => 𝓕 f (-w) := funext (Real.fourierInv_eq_fourier_neg f)
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact h1.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure V))
  · rw [← h2]
    exact integral_neg_eq_self (fun w => ‖𝓕 f w‖ ^ 2) volume

end MellinPlancherel

namespace MellinPlancherel

noncomputable def lineProfile (σ : ℝ) (a : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * a t

noncomputable def charIntegral (a : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * a t

/--
@isnad1 id=eq.0h3v.s6.10ad8be61107 from=translated src=- shape=617c386e vocab=c87e7d45
-/
theorem cpow_exp_eq (σ u t : ℝ) :
    ((Real.exp u : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.exp (σ * u) : ℝ) : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_exp, mul_add, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul]
  congr 1 <;> (congr 1; ring)

/--
@isnad1 id=eq.0h3v.s5.217e7db7740e from=translated src=- shape=401de007 vocab=9e557ebf
-/
theorem lineProfile_exp (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) :
    lineProfile σ a (Real.exp u) = ((Real.exp (σ * u) : ℝ) : ℂ) * charIntegral a u := by
  unfold lineProfile charIntegral
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [cpow_exp_eq, mul_assoc]

/--
@isnad1 id=eq.0h2v.s5.13716c438b42 from=translated src=- shape=009cfa76 vocab=08ebda01
-/
theorem charIntegral_two_pi_mul (a : ℝ → ℂ) (w : ℝ) : charIntegral a (2 * π * w) = 𝓕⁻ a w := by
  rw [Real.fourierInv_eq']
  unfold charIntegral
  have h : ∀ t : ℝ, ((t * (2 * π * w) : ℝ) : ℂ) = ((2 * π * inner ℝ t w : ℝ) : ℂ) := fun t => by
    rw [Real.inner_apply]
    push_cast
    ring
  simp_rw [h, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s6.edcd5b6da746 from=translated src=- shape=a6b8f389 vocab=de3c61ee
-/
theorem collapse (σ : ℝ) (a : ℝ → ℂ) (u : ℝ) :
    |Real.exp u| • ((Real.exp u ^ (-(2 * σ)) / Real.exp u) * ‖lineProfile σ a (Real.exp u)‖ ^ 2)
      = ‖charIntegral a u‖ ^ 2 := by
  rw [lineProfile_exp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    smul_eq_mul, mul_pow]
  have hs : |Real.exp u| * (Real.exp u ^ (-(2 * σ)) / Real.exp u) * Real.exp (σ * u) ^ 2 = 1 := by
    rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg, pow_two]
    simp only [← Real.exp_add]
    rw [← Real.exp_zero]
    congr 1
    ring
  linear_combination (‖charIntegral a u‖ ^ 2) * hs

/--
@isnad1 id=and.2h2v.s8.2e5559c127e6 from=translated src=- shape=694ec76f vocab=d6bfc647
-/
theorem integrableOn_and_setIntegral (σ : ℝ) (a : ℝ → ℂ) (ha : Integrable a) (ha2 : MemLp a 2) :
    IntegrableOn (fun y : ℝ => (y ^ (-(2 * σ)) / y) * ‖lineProfile σ a y‖ ^ 2) (Set.Ioi 0) ∧
    ∫ y in Set.Ioi (0 : ℝ), (y ^ (-(2 * σ)) / y) * ‖lineProfile σ a y‖ ^ 2
      = 2 * π * ∫ t : ℝ, ‖a t‖ ^ 2 := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  obtain ⟨hF2, hFeq⟩ := memLp_two_fourierInv_and_integral_norm_sq_eq a ha ha2

  have hFint : Integrable (fun w : ℝ => ‖𝓕⁻ a w‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF2.1).mp hF2
  have hCint : Integrable (fun u : ℝ => ‖charIntegral a u‖ ^ 2) := by
    have h3 : Integrable (fun w : ℝ => ‖charIntegral a (2 * π * w)‖ ^ 2) := by
      simpa only [charIntegral_two_pi_mul] using hFint
    exact (integrable_comp_mul_left_iff (fun u : ℝ => ‖charIntegral a u‖ ^ 2) h2π).mp h3
  refine ⟨?_, ?_⟩
  · rw [himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj,
      integrableOn_univ]
    simp_rw [collapse]
    exact hCint
  · calc ∫ y in Set.Ioi (0 : ℝ), (y ^ (-(2 * σ)) / y) * ‖lineProfile σ a y‖ ^ 2
        = ∫ u : ℝ, ‖charIntegral a u‖ ^ 2 := by
          rw [himage, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
            Measure.restrict_univ]
          exact integral_congr_ae (Filter.Eventually.of_forall (collapse σ a))
      _ = |2 * π| • ∫ w : ℝ, ‖charIntegral a (2 * π * w)‖ ^ 2 := by
          rw [Measure.integral_comp_mul_left (fun u : ℝ => ‖charIntegral a u‖ ^ 2) (2 * π),
            smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h2π), one_smul]
      _ = 2 * π * ∫ t : ℝ, ‖a t‖ ^ 2 := by
          simp_rw [charIntegral_two_pi_mul]
          rw [hFeq, abs_of_pos (by positivity), smul_eq_mul]

end MellinPlancherel

open MeasureTheory

/--
@isnad1 id=and.2h2v.s8.6b1471549eeb from=translated src=- shape=4832f28c vocab=4f07d2fe
-/
theorem solution
    (σ : ℝ) (a : ℝ → ℂ) (_ha : Integrable a) (_ha2 : MemLp a 2) :
    IntegrableOn (fun y : ℝ => (y ^ (-(2 * σ)) / y) *
        ‖∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * a t‖ ^ 2) (Set.Ioi 0) ∧
    ∫ y in Set.Ioi (0 : ℝ), (y ^ (-(2 * σ)) / y) *
        ‖∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * a t‖ ^ 2
      = 2 * Real.pi * ∫ t : ℝ, ‖a t‖ ^ 2 :=
  MellinPlancherel.integrableOn_and_setIntegral σ a _ha _ha2
