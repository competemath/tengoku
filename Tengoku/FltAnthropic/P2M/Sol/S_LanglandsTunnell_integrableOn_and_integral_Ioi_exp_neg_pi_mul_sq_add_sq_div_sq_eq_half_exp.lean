import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Function.JacobianOneDim

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_integrableOn_and_integral_Ioi_exp_neg_pi_mul_sq_add_sq_div_sq_eq_half_exp

set_option autoImplicit false

open MeasureTheory Set Real

namespace SchlomilchGauss

noncomputable def phi (ρ w : ℝ) : ℝ := w - ρ * w⁻¹

/--
@isnad1 id=hasderiv.1h2v.s6.44de7e13ad86 from=translated src=- shape=19474197 vocab=4662ad3a
-/
theorem hasDerivAt_phi (ρ : ℝ) {w : ℝ} (hw : w ≠ 0) :
    HasDerivAt (phi ρ) (1 + ρ * (w ^ 2)⁻¹) w := by
  have h := (hasDerivAt_id w).sub ((hasDerivAt_inv hw).const_mul ρ)
  convert h using 1
  · rfl
  · rfl
  · rfl
  ring

/--
@isnad1 id=eq.1h2v.s7.363c5f8bb518 from=translated src=- shape=5c420439 vocab=e168480d
-/
theorem phi_sq (ρ : ℝ) {w : ℝ} (hw : w ≠ 0) : (phi ρ w) ^ 2 = w ^ 2 + ρ ^ 2 / w ^ 2 - 2 * ρ := by
  unfold phi; field_simp; ring

/--
@isnad1 id=injon.1h1v.s4.de90520e001b from=translated src=- shape=e4f1f832 vocab=1a6b59cd
-/
theorem injOn_phi {ρ : ℝ} (hρ : 0 < ρ) : InjOn (phi ρ) (Ioi 0) := by
  intro x hx y hy hxy
  have hx : 0 < x := hx
  have hy : 0 < y := hy
  unfold phi at hxy
  have h : (x - y) * (x * y + ρ) = 0 := by
    field_simp at hxy
    nlinarith [hxy]
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith [mul_pos hx hy]

/--
@isnad1 id=eq.1h1v.s5.9b476f6f8364 from=translated src=- shape=3fe21853 vocab=54342d07
-/
theorem image_phi {ρ : ℝ} (hρ : 0 < ρ) : phi ρ '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun t => ?_
  set r : ℝ := Real.sqrt (t ^ 2 + 4 * ρ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = t ^ 2 + 4 * ρ := Real.sq_sqrt (by positivity)
  have hrt : |t| < r := by
    rw [← Real.sqrt_sq_eq_abs, hr]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  set w : ℝ := (t + r) / 2 with hw
  have hw0 : 0 < w := by
    rw [hw]; have := neg_abs_le t; linarith
  refine ⟨w, hw0, ?_⟩
  unfold phi
  have hw2 : w ^ 2 - t * w - ρ = 0 := by rw [hw]; nlinarith [hr2]
  field_simp
  nlinarith [hw2, hw0]

/--
@isnad1 id=eq.1h1v.s5.8592e54232c1 from=translated src=- shape=70860b5d vocab=9504c147
-/
theorem image_inv {ρ : ℝ} (hρ : 0 < ρ) : (fun u : ℝ => ρ * u⁻¹) '' Ioi 0 = Ioi 0 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩; exact mul_pos hρ (inv_pos.mpr hu)
  · intro hx
    refine ⟨ρ * x⁻¹, mul_pos hρ (inv_pos.mpr hx), ?_⟩
    have : x ≠ 0 := ne_of_gt hx
    field_simp

/--
@isnad1 id=injon.1h1v.s5.99c2a0948779 from=translated src=- shape=18dddd97 vocab=bf3060b7
-/
theorem injOn_inv {ρ : ℝ} (hρ : 0 < ρ) : InjOn (fun u : ℝ => ρ * u⁻¹) (Ioi 0) := by
  intro x hx y hy hxy
  have hx' : x ≠ 0 := ne_of_gt hx
  have hy' : y ≠ 0 := ne_of_gt hy
  have := congrArg (fun z => ρ * z⁻¹) hxy
  simp only [mul_inv, inv_inv] at this
  field_simp at this
  linarith [this]

/--
@isnad1 id=eq.2h2v.s5.ca3e0e853424 from=translated src=- shape=9dd67643 vocab=48176043
-/
theorem phi_inv (ρ : ℝ) {u : ℝ} (hu : u ≠ 0) (hρ : ρ ≠ 0) : phi ρ (ρ * u⁻¹) = -phi ρ u := by
  unfold phi; field_simp; ring

noncomputable def G (ρ w : ℝ) : ℝ := Real.exp (-(Real.pi * (phi ρ w) ^ 2))

/--
@isnad1 id=lt.0h2v.s4.c9b6ccf9e007 from=translated src=- shape=a120b2a8 vocab=3ec1b6a4
-/
theorem G_pos (ρ w : ℝ) : 0 < G ρ w := Real.exp_pos _

/--
@isnad1 id=continuo.0h1v.s4.633cabbf5a2f from=translated src=- shape=140225b6 vocab=b47fbc1c
-/
theorem continuousOn_G (ρ : ℝ) : ContinuousOn (G ρ) (Ioi 0) := by
  intro w hw
  have hw : (w : ℝ) ≠ 0 := ne_of_gt hw
  apply ContinuousAt.continuousWithinAt
  unfold G phi
  fun_prop (disch := exact hw)

/--
@isnad1 id=eq.0h0v.s5.d07d29741687 from=translated src=- shape=d399efb6 vocab=c08a8a47
-/
theorem gaussian_one : ∫ t : ℝ, Real.exp (-(Real.pi * t ^ 2)) = 1 := by
  have h := integral_gaussian Real.pi
  rw [div_self Real.pi_ne_zero, Real.sqrt_one] at h
  simpa only [neg_mul] using h

/--
@isnad1 id=integrab.0h0v.s5.e94af43f9f26 from=translated src=- shape=62874e93 vocab=dc82ca3d
-/
theorem integrable_gaussian' : Integrable (fun t : ℝ => Real.exp (-(Real.pi * t ^ 2))) := by
  simpa only [neg_mul] using integrable_exp_neg_mul_sq Real.pi_pos

/--
@isnad1 id=and.1h1v.s6.7bb566912f9f from=translated src=- shape=af8cd16a vocab=94f85079
-/
theorem integrableOn_G_and_integral {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (G ρ) (Ioi 0) ∧ ∫ w in Ioi (0 : ℝ), G ρ w = 1 / 2 := by
  have hderiv : ∀ w ∈ Ioi (0 : ℝ), HasDerivWithinAt (phi ρ) (1 + ρ * (w ^ 2)⁻¹) (Ioi 0) w :=
    fun w hw => (hasDerivAt_phi ρ (ne_of_gt hw)).hasDerivWithinAt

  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv (injOn_phi hρ)
    (fun t => Real.exp (-(Real.pi * t ^ 2)))
  rw [image_phi hρ, Measure.restrict_univ, gaussian_one] at hcv
  have hint : IntegrableOn (fun w : ℝ => |1 + ρ * (w ^ 2)⁻¹| • Real.exp (-(Real.pi * (phi ρ w) ^ 2))) (Ioi 0) := by
    have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv (injOn_phi hρ)
      (fun t => Real.exp (-(Real.pi * t ^ 2)))).mp (by rw [image_phi hρ]; exact integrable_gaussian'.integrableOn)
    exact this
  have habs : ∀ w : ℝ, 0 < w → |1 + ρ * (w ^ 2)⁻¹| = 1 + ρ * (w ^ 2)⁻¹ := fun w hw => abs_of_pos (by positivity)
  have hint' : IntegrableOn (fun w : ℝ => (1 + ρ * (w ^ 2)⁻¹) * G ρ w) (Ioi 0) := by
    refine hint.congr_fun (fun w hw => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, habs w hw, G]
  have hmeasG : AEStronglyMeasurable (G ρ) (volume.restrict (Ioi 0)) := (continuousOn_G ρ).aestronglyMeasurable measurableSet_Ioi
  have hG : IntegrableOn (G ρ) (Ioi 0) := by
    refine Integrable.mono' hint' hmeasG ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw : 0 < w := hw
    rw [Real.norm_eq_abs, abs_of_pos (G_pos ρ w)]
    have := G_pos ρ w
    nlinarith [show 0 ≤ ρ * (w ^ 2)⁻¹ by positivity]
  have hG2 : IntegrableOn (fun w : ℝ => ρ * (w ^ 2)⁻¹ * G ρ w) (Ioi 0) := by
    refine Integrable.mono' hint' ?_ ?_
    · exact ((continuousOn_const.mul ((continuousOn_pow 2).inv₀ fun w hw => pow_ne_zero 2 (ne_of_gt (show (0 : ℝ) < w from hw)))).mul
        (continuousOn_G ρ)).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hw : 0 < w := hw
      have h1 : 0 ≤ ρ * (w ^ 2)⁻¹ * G ρ w := by have := G_pos ρ w; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      nlinarith [G_pos ρ w]

  have hderiv2 : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => ρ * u⁻¹) (ρ * (-(u ^ 2)⁻¹)) (Ioi 0) u :=
    fun u hu => ((hasDerivAt_inv (ne_of_gt hu)).const_mul ρ).hasDerivWithinAt
  have hcv2 := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv2 (injOn_inv hρ) (G ρ)
  rw [image_inv hρ] at hcv2
  have hrefl : ∫ u in Ioi (0 : ℝ), ρ * (u ^ 2)⁻¹ * G ρ u = ∫ x in Ioi (0 : ℝ), G ρ x := by
    rw [hcv2]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu : 0 < u := hu
    rw [smul_eq_mul, show ρ * (-(u ^ 2)⁻¹) = -(ρ * (u ^ 2)⁻¹) by ring, abs_neg, abs_of_pos (by positivity)]
    congr 1
    simp only [G, phi_inv ρ hu.ne' hρ.ne', neg_sq]

  refine ⟨hG, ?_⟩
  have hsum : ∫ w in Ioi (0 : ℝ), (1 + ρ * (w ^ 2)⁻¹) * G ρ w =
      (∫ w in Ioi (0 : ℝ), G ρ w) + ∫ w in Ioi (0 : ℝ), ρ * (w ^ 2)⁻¹ * G ρ w := by
    rw [← integral_add hG hG2]
    refine setIntegral_congr_fun measurableSet_Ioi fun w _ => ?_
    ring
  have hcv' : ∫ w in Ioi (0 : ℝ), (1 + ρ * (w ^ 2)⁻¹) * G ρ w = 1 := by
    refine Eq.trans ?_ hcv.symm
    refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
    simp only [smul_eq_mul, habs w hw, G]
  rw [hrefl] at hsum
  linarith

end SchlomilchGauss

open SchlomilchGauss in
/--
@isnad1 id=and.1h1v.s8.57f7f394332d from=translated src=- shape=7a916a01 vocab=69a3f58f
-/
theorem solution (ρ : ℝ) (hρ : 0 < ρ) :
    IntegrableOn (fun w : ℝ => Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2)))) (Ioi 0) ∧
      ∫ w in Ioi (0 : ℝ), Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) =
        (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * ρ)) := by
  obtain ⟨hG, hval⟩ := integrableOn_G_and_integral hρ
  have hpt : ∀ w ∈ Ioi (0 : ℝ), Real.exp (-(Real.pi * (w ^ 2 + ρ ^ 2 / w ^ 2))) = Real.exp (-(2 * Real.pi * ρ)) * G ρ w := by
    intro w hw
    have hw : (w : ℝ) ≠ 0 := ne_of_gt hw
    rw [G, ← Real.exp_add, phi_sq ρ hw]
    congr 1
    ring
  constructor
  · have h1 : IntegrableOn (fun w => Real.exp (-(2 * Real.pi * ρ)) * G ρ w) (Ioi 0) volume :=
      hG.const_mul (Real.exp (-(2 * Real.pi * ρ)))
    exact h1.congr_fun (fun w hw => (hpt w hw).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hval]
    ring
