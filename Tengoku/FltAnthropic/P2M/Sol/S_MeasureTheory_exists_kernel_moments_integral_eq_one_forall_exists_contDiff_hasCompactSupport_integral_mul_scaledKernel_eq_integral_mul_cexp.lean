import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_exists_kernel_moments_integral_eq_one_forall_exists_contDiff_hasCompactSupport_integral_mul_scaledKernel_eq_integral_mul_cexp

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate ContDiff

namespace BK9

open scoped FourierTransform RealInnerProductSpace

noncomputable def g₀ : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def g (x : ℝ) : ℂ := ((g₀ : ℝ → ℝ) x : ℂ)

/--
@isnad1 id=contdiff.0h0v.s5.6ffae8d912ca from=translated src=- shape=352d7a74 vocab=b5a71102
-/
lemma g_contDiff : ContDiff ℝ ∞ g := Complex.ofRealCLM.contDiff.comp g₀.contDiff

/--
@isnad1 id=continuo.0h0v.s4.279dab065916 from=translated src=- shape=54c8eceb vocab=1c31b387
-/
lemma g_continuous : Continuous g := g_contDiff.continuous

/--
@isnad1 id=hascompa.0h0v.s3.88b82722b736 from=translated src=- shape=54c8eceb vocab=f8621e64
-/
lemma g_hasCompactSupport : HasCompactSupport g :=
  g₀.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero

/--
@isnad1 id=eq.0h0v.s3.90a115278a9a from=translated src=- shape=1ac31801 vocab=53ea8dc5
-/
lemma g_zero : g 0 = 1 := by
  unfold g
  rw [g₀.one_of_mem_closedBall (Metric.mem_closedBall_self g₀.rIn_pos.le)]
  simp

/--
@isnad1 id=eq.0h1v.s5.68857dad53b4 from=translated src=- shape=f68c6383 vocab=6408e787
-/
lemma conj_g (x : ℝ) : conj (g x) = g x := by unfold g; exact Complex.conj_ofReal _

/--
@isnad1 id=integrab.0h0v.s5.ea5f2a26ed39 from=translated src=- shape=c57f8401 vocab=6463ee00
-/
lemma g_integrable : Integrable g := g_continuous.integrable_of_hasCompactSupport g_hasCompactSupport

/--
@isnad1 id=hascompa.0h1v.s4.05527aa2d573 from=translated src=- shape=9e39cfad vocab=29ffe08b
-/
lemma iteratedDeriv_g_hasCompactSupport (n : ℕ) : HasCompactSupport (iteratedDeriv n g) := by
  have h := (g_hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) n).comp_left
    (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => L fun _ => 1) (by simp)
  have : iteratedDeriv n g = (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => L fun _ => 1) ∘
      iteratedFDeriv ℝ n g := by
    funext x; rw [iteratedDeriv_eq_iteratedFDeriv]; rfl
  rw [this]; exact h

/--
@isnad1 id=integrab.0h1v.s5.91c42225d0c4 from=translated src=- shape=3e90c28e vocab=46f00958
-/
lemma iteratedDeriv_g_integrable (n : ℕ) : Integrable (iteratedDeriv n g) :=
  (g_contDiff.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (iteratedDeriv_g_hasCompactSupport n)

noncomputable def Φ : ℝ → ℂ := 𝓕 g

noncomputable def ρ (t : ℝ) : ℝ := (Φ t).re

/--
@isnad1 id=continuo.0h0v.s4.24ee3c2e5aa6 from=translated src=- shape=54c8eceb vocab=0cda2846
-/
lemma Φ_continuous : Continuous Φ :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ g_integrable

/--
@isnad1 id=continuo.0h0v.s3.73b9ac410274 from=translated src=- shape=e3d48bcb vocab=958ff3ed
-/
lemma ρ_continuous : Continuous ρ := Complex.continuous_re.comp Φ_continuous

/--
@isnad1 id=ex.0h1v.s5.2608c3b5e2e6 from=translated src=- shape=eca7c75d vocab=f32493bf
-/
lemma Φ_decay (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, |w| ^ n * ‖Φ w‖ ≤ C := by
  have key := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (n := n) g_contDiff
    (fun k _ => iteratedDeriv_g_integrable k) le_top
  set L : ℝ := ∫ v : ℝ, ‖iteratedDeriv n g v‖ with hL
  refine ⟨L / (2 * Real.pi) ^ n, by positivity, fun w => ?_⟩
  have h1 : ‖𝓕 (iteratedDeriv n g) w‖ ≤ L :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  rw [key] at h1
  simp only [norm_smul, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos] at h1
  rw [le_div_iff₀ (by positivity)]
  calc |w| ^ n * ‖Φ w‖ * (2 * Real.pi) ^ n = (2 * Real.pi * |w|) ^ n * ‖𝓕 g w‖ := by rw [Φ]; ring
    _ ≤ L := h1

/--
@isnad1 id=ex.0h1v.s6.9fb83e5da3f8 from=translated src=- shape=7bd46aa0 vocab=1cb6f591
-/
lemma Φ_decay₂ (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, |w| ^ n * ‖Φ w‖ ≤ C * (1 + w ^ 2)⁻¹ := by
  obtain ⟨C₀, hC₀, h₀⟩ := Φ_decay n
  obtain ⟨C₂, hC₂, h₂⟩ := Φ_decay (n + 2)
  refine ⟨C₀ + C₂, by positivity, fun w => ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have := h₂ w
  have e : |w| ^ (n + 2) = |w| ^ n * w ^ 2 := by rw [pow_add, sq_abs]
  rw [e] at this
  nlinarith [h₀ w, norm_nonneg (Φ w), pow_nonneg (abs_nonneg w) n]

/--
@isnad1 id=integrab.0h1v.s5.1e850e313ef4 from=translated src=- shape=b0117740 vocab=8376f977
-/
lemma integrable_pow_mul_norm_Φ (n : ℕ) : Integrable (fun t : ℝ => |t| ^ n * ‖Φ t‖) := by
  obtain ⟨C, hC, h⟩ := Φ_decay₂ n
  refine ((integrable_inv_one_add_sq).const_mul C).mono' ?_ (ae_of_all _ fun t => ?_)
  · exact ((continuous_abs.pow n).mul Φ_continuous.norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]; exact h t

/--
@isnad1 id=integrab.0h0v.s5.66b382ef485d from=translated src=- shape=c57f8401 vocab=2d6ee5ff
-/
lemma Φ_integrable : Integrable Φ := by
  refine (integrable_pow_mul_norm_Φ 0).mono' Φ_continuous.aestronglyMeasurable (ae_of_all _ fun t => ?_)
  simp

/--
@isnad1 id=integrab.0h1v.s5.1880303b6293 from=translated src=- shape=121683b3 vocab=9950a642
-/
lemma ρ_moment (n : ℕ) : Integrable (fun t : ℝ => |t| ^ n * ρ t) := by
  refine (integrable_pow_mul_norm_Φ n).mono' ((continuous_abs.pow n).mul ρ_continuous).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)

/--
@isnad1 id=eq.0h0v.s5.873dd846485f from=translated src=- shape=f0e61117 vocab=b3cba564
-/
lemma integral_ρ : ∫ t : ℝ, ρ t = 1 := by
  have h1 : ∫ t : ℝ, ρ t = (∫ t : ℝ, Φ t).re := by
    unfold ρ
    exact integral_re Φ_integrable
  have h2 : ∫ t : ℝ, Φ t = 𝓕⁻ Φ 0 := by
    rw [Real.fourierInv_eq]
    simp
  have h3 : 𝓕⁻ Φ 0 = g 0 := by
    unfold Φ
    rw [g_continuous.fourierInv_fourier_eq g_integrable Φ_integrable]
  rw [h1, h2, h3, g_zero, Complex.one_re]

noncomputable def Gs (δ : ℝ) (z : ℝ) : ℂ :=
  (g ((δ / (2 * Real.pi)) * z) + g ((-(δ / (2 * Real.pi))) * z)) / 2

/--
@isnad1 id=hascompa.1h1v.s5.aa1c87bf82b1 from=translated src=- shape=4bd99e0f vocab=202015e9
-/
lemma hasCompactSupport_g_comp (c : ℝ) (hc : c ≠ 0) : HasCompactSupport (fun z : ℝ => g (c * z)) :=
  g_hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft₀ c hc)

/--
@isnad1 id=continuo.0h1v.s5.c8a874e8e08e from=translated src=- shape=43976749 vocab=89f70dd2
-/
lemma continuous_g_comp (c : ℝ) : Continuous (fun z : ℝ => g (c * z)) :=
  g_continuous.comp (continuous_const.mul continuous_id)

/--
@isnad1 id=contdiff.0h1v.s5.33fe140b69db from=translated src=- shape=7c59f4db vocab=dcab993c
-/
lemma contDiff_g_comp (c : ℝ) : ContDiff ℝ ∞ (fun z : ℝ => g (c * z)) :=
  g_contDiff.comp (contDiff_const.mul contDiff_id)

/--
@isnad1 id=contdiff.0h1v.s5.ade32f55b811 from=translated src=- shape=ba16b31b vocab=464a6588
-/
lemma Gs_contDiff (δ : ℝ) : ContDiff ℝ ∞ (Gs δ) :=
  ((contDiff_g_comp _).add (contDiff_g_comp _)).div_const _

/--
@isnad1 id=continuo.0h1v.s4.a8d5ee11a593 from=translated src=- shape=9bb0b988 vocab=f9292330
-/
lemma Gs_continuous (δ : ℝ) : Continuous (Gs δ) := (Gs_contDiff δ).continuous

/--
@isnad1 id=hascompa.1h1v.s4.c00cdfdeb9b1 from=translated src=- shape=b8038e13 vocab=12dd036a
-/
lemma Gs_hasCompactSupport (δ : ℝ) (hδ : 0 < δ) : HasCompactSupport (Gs δ) := by
  have h1 := hasCompactSupport_g_comp (δ / (2 * Real.pi)) (by positivity)
  have h2 := hasCompactSupport_g_comp (-(δ / (2 * Real.pi))) (by
    have : 0 < δ / (2 * Real.pi) := by positivity
    linarith)
  exact ((h1.add h2).mul_left (f := fun _ => (1 / 2 : ℂ))).mono (by
    intro z hz
    simp only [Function.mem_support, Gs] at hz ⊢
    intro h; apply hz; rw [show (g (δ / (2 * Real.pi) * z) + g (-(δ / (2 * Real.pi)) * z)) = 0 by
      simpa using h]; simp)

/--
@isnad1 id=integrab.1h1v.s5.06e016659750 from=translated src=- shape=b07cb5a9 vocab=ac26ee42
-/
lemma Gs_integrable (δ : ℝ) (hδ : 0 < δ) : Integrable (Gs δ) :=
  (Gs_continuous δ).integrable_of_hasCompactSupport (Gs_hasCompactSupport δ hδ)

/--
@isnad1 id=eq.0h1v.s6.9cd44cc45386 from=translated src=- shape=65b44418 vocab=32283693
-/
lemma Φ_eq (w : ℝ) : Φ w = ∫ v : ℝ, Complex.exp (((-2 * Real.pi * v * w : ℝ) : ℂ) * Complex.I) * g v := by
  unfold Φ
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]

/--
@isnad1 id=eq.0h1v.s6.1d330c36cb02 from=translated src=- shape=0f22fb1b vocab=8ae00bef
-/
lemma conj_Φ_eq (w : ℝ) : conj (Φ w) = ∫ v : ℝ, Complex.exp (((2 * Real.pi * v * w : ℝ) : ℂ) * Complex.I) * g v := by
  rw [Φ_eq, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [map_mul, conj_g]
  rw [← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/--
@isnad1 id=eq.1h2v.s6.111698bcfa86 from=translated src=- shape=35e34dd7 vocab=08a29d62
-/
lemma integral_subst (c : ℝ) (hc : c ≠ 0) (F : ℝ → ℂ) :
    ∫ v : ℝ, F v = |c| * ∫ z : ℝ, F (c * z) := by
  have := Measure.integral_comp_mul_left F c
  rw [this, abs_inv, Complex.real_smul, ← mul_assoc]
  rw [show ((|c| : ℝ) : ℂ) * ((|c|⁻¹ : ℝ) : ℂ) = 1 by
    push_cast; field_simp [abs_ne_zero.mpr hc]]
  rw [one_mul]

/--
@isnad1 id=eq.1h2v.s6.04f7948d18e9 from=translated src=- shape=51a63c35 vocab=af7d4a39
-/
lemma kernel_identity (δ : ℝ) (hδ : 0 < δ) (s : ℝ) :
    ((δ⁻¹ * ρ (s / δ) : ℝ) : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) * ∫ z : ℝ, Gs δ z * Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  set c : ℝ := δ / (2 * Real.pi) with hcdef
  have hc : 0 < c := by positivity

  have hρ : ((ρ (s / δ) : ℝ) : ℂ) = (Φ (s / δ) + conj (Φ (s / δ))) / 2 := by
    unfold ρ; rw [Complex.re_eq_add_conj]

  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have e1 : Φ (s / δ) = ((c : ℝ) : ℂ) * ∫ z : ℝ, Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z) := by
    rw [Φ_eq, integral_subst (-c) (by linarith) _, abs_neg, abs_of_pos hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show Complex.exp (((-2 * Real.pi * ((-c) * z) * (s / δ) : ℝ) : ℂ) * Complex.I) * g ((-c) * z) =
      Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z)
    have hX : ((-2 * Real.pi * ((-c) * z) * (s / δ) : ℝ) : ℂ) * Complex.I = (s : ℂ) * Complex.I * (z : ℂ) := by
      rw [hcdef]; push_cast; field_simp
    rw [hX]
  have e2 : conj (Φ (s / δ)) = ((c : ℝ) : ℂ) * ∫ z : ℝ, Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z) := by
    rw [conj_Φ_eq, integral_subst c hc.ne' _, abs_of_pos hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show Complex.exp (((2 * Real.pi * (c * z) * (s / δ) : ℝ) : ℂ) * Complex.I) * g (c * z) =
      Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z)
    have hX : ((2 * Real.pi * (c * z) * (s / δ) : ℝ) : ℂ) * Complex.I = (s : ℂ) * Complex.I * (z : ℂ) := by
      rw [hcdef]; push_cast; field_simp
    rw [hX]
  have hi1 : Integrable (fun z : ℝ => Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z)) :=
    ((Complex.continuous_exp.comp ((continuous_const).mul Complex.continuous_ofReal)).mul
      (continuous_g_comp _)).integrable_of_hasCompactSupport
      ((hasCompactSupport_g_comp (-c) (by linarith)).mul_left)
  have hi2 : Integrable (fun z : ℝ => Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z)) :=
    ((Complex.continuous_exp.comp ((continuous_const).mul Complex.continuous_ofReal)).mul
      (continuous_g_comp _)).integrable_of_hasCompactSupport
      ((hasCompactSupport_g_comp c hc.ne').mul_left)
  rw [Complex.ofReal_mul, hρ, e2, e1, ← mul_add, ← integral_add hi1 hi2]
  have e3 : ∫ z : ℝ, Gs δ z * Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) =
      (1 / 2 : ℂ) * ∫ z : ℝ, (Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g ((-c) * z) +
        Complex.exp ((s : ℂ) * Complex.I * (z : ℂ)) * g (c * z)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Gs, hcdef]
    ring
  rw [e3, hcdef]
  push_cast
  field_simp

/--
@isnad1 id=eq.0h2v.s5.bfa659ca7932 from=translated src=- shape=6352d428 vocab=d6b61dc0
-/
lemma norm_cexp_mul_I_mul (a z : ℝ) : ‖Complex.exp ((a : ℂ) * Complex.I * (z : ℂ))‖ = 1 := by
  rw [show (a : ℂ) * Complex.I * (z : ℂ) = ((a * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/--
@isnad1 id=integrab.3h4v.s6.1c366789d14c from=translated src=- shape=8dcd4a33 vocab=d050ac61
-/
lemma integrable_pow_mul_norm_of_bdd {u : ℝ → ℂ} (hu : Measurable u) {R B : ℝ}
    (hR : ∀ x, R < |x| → u x = 0) (hB : ∀ x, ‖u x‖ ≤ B) (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ n * ‖u x‖) := by
  have hB0 : ∀ x, 0 ≤ B := fun x => (norm_nonneg _).trans (hB x)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖x‖ ^ n * ‖u x‖) volume :=
    ((continuous_norm.pow n).measurable.mul hu.norm).aestronglyMeasurable
  refine (((integrableOn_const (measure_Icc_lt_top (a := -R) (b := R)).ne).integrable_indicator
    measurableSet_Icc : Integrable ((Set.Icc (-R) R).indicator fun _ => |R| ^ n * B))).mono'
    hmeas (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) n) (norm_nonneg _))]
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem hx]
    have : ‖x‖ ≤ |R| := by rw [Real.norm_eq_abs]; exact (abs_le.mpr hx).trans (le_abs_self R)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) this n) (hB x) (norm_nonneg _) (by positivity)
  · rw [Set.indicator_of_notMem hx]
    have : R < |x| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
      · exact lt_of_lt_of_le h (le_abs_self x)
    rw [hR x this, norm_zero, mul_zero]

end BK9

/--
@isnad1 id=ex.0h0v.s8.459714ad6a1d from=translated src=- shape=60d98d46 vocab=1cb2020d
-/
theorem solution :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t)) ∧ (∫ t : ℝ, ρ t = 1) ∧
      ∀ (u : ℝ → ℂ), Measurable u → (∃ R : ℝ, ∀ x, R < |x| → u x = 0) → (∃ B : ℝ, ∀ x, ‖u x‖ ≤ B) →
      ∀ δ : ℝ, 0 < δ →
      ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧
        ∀ t : ℝ, (∫ x : ℝ, u x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) =
          ∫ x : ℝ, h x * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) := by
  open scoped FourierTransform in
  refine ⟨BK9.ρ, BK9.ρ_continuous.measurable, BK9.ρ_moment, BK9.integral_ρ, ?_⟩
  intro u hu hR hB δ hδ
  obtain ⟨R, hR⟩ := hR
  obtain ⟨B, hB⟩ := hB
  have hmom : ∀ n : ℕ, Integrable (fun x : ℝ => ‖x‖ ^ n * ‖u x‖) :=
    fun n => BK9.integrable_pow_mul_norm_of_bdd hu hR hB n
  have hu_int : Integrable u := (hmom 0).mono' hu.aestronglyMeasurable (ae_of_all _ fun x => by simp)
  have hFu : ContDiff ℝ ∞ (𝓕 u) := Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun n _ => hmom n)
  set h : ℝ → ℂ := fun z => (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * (BK9.Gs δ z * 𝓕 u (z / (2 * Real.pi))) with hh
  refine ⟨h, ?_, ?_, ?_⟩
  · exact contDiff_const.mul ((BK9.Gs_contDiff δ).mul (hFu.comp (contDiff_id.div_const _)))
  · have : HasCompactSupport (fun z : ℝ => BK9.Gs δ z * 𝓕 u (z / (2 * Real.pi))) :=
      (BK9.Gs_hasCompactSupport δ hδ).mul_right
    exact this.mul_left
  · intro t

    set F : ℝ → ℝ → ℂ := fun x z => (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      (u x * (BK9.Gs δ z * Complex.exp (((t - x : ℝ) : ℂ) * Complex.I * (z : ℂ)))) with hF
    have step1 : (∫ x : ℝ, u x * ((δ⁻¹ * BK9.ρ ((t - x) / δ) : ℝ) : ℂ)) = ∫ x : ℝ, ∫ z : ℝ, F x z := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hF]
      rw [BK9.kernel_identity δ hδ (t - x), ← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only
      ring
    have hFint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod volume) := by
      have hg : Integrable (fun p : ℝ × ℝ => (2 * Real.pi)⁻¹ * (‖u p.1‖ * ‖BK9.Gs δ p.2‖)) ((volume : Measure ℝ).prod volume) :=
        (hu_int.norm.mul_prod (BK9.Gs_integrable δ hδ).norm).const_mul _
      refine hg.mono' ?_ (ae_of_all _ fun p => ?_)
      · have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1) ((volume : Measure ℝ).prod volume) :=
          (hu.comp measurable_fst).aestronglyMeasurable
        have m2 : Continuous (fun p : ℝ × ℝ => BK9.Gs δ p.2 *
            Complex.exp (((t - p.1 : ℝ) : ℂ) * Complex.I * (p.2 : ℂ))) := by
          refine ((BK9.Gs_continuous δ).comp continuous_snd).mul (Complex.continuous_exp.comp ?_)
          exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul continuous_const).mul
            (Complex.continuous_ofReal.comp continuous_snd)
        exact (m1.mul m2.aestronglyMeasurable).const_mul _
      · rcases p with ⟨x, z⟩
        simp only [Function.uncurry_apply_pair, hF, norm_mul, BK9.norm_cexp_mul_I_mul, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        exact le_rfl
    rw [step1, integral_integral_swap hFint]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)

    have hpt : ∀ x : ℝ, F x z = ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) * BK9.Gs δ z * Complex.exp ((t : ℂ) * Complex.I * (z : ℂ))) *
        (Complex.exp (((-2 * Real.pi * x * (z / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) • u x) := by
      intro x
      simp only [hF, smul_eq_mul]
      have : Complex.exp (((t - x : ℝ) : ℂ) * Complex.I * (z : ℂ)) =
          Complex.exp ((t : ℂ) * Complex.I * (z : ℂ)) * Complex.exp (((-2 * Real.pi * x * (z / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        have hπC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        push_cast
        field_simp
        ring
      rw [this]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, ← Real.fourier_real_eq_integral_exp_smul]
    simp only [hh]
    ring
