import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Spectrum

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma polar_symm_circle (p : ℝ × ℝ) : Complex.polarCoord.symm p = circlePoint p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply,circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma disk_lintegral_le_polar (F : ℂ → ℝ≥0∞) :
    (∫⁻ z in disk, F z) ≤ ∫⁻ r in Ioo (0:ℝ) 1,
      ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi, F (circlePoint r θ) := by
  have hm : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [← lintegral_indicator hm,← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) ≤ _
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have he : (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) =
      (Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (circlePoint p.1 p.2)) := by
    ext p
    simp_rw [polar_symm_circle]
    by_cases h0 : 0 < p.1
    · have hd : circlePoint p.1 p.2 ∈ disk ↔ p.1 < 1 := by
        simp [disk,circlePoint_norm,abs_of_pos h0]
      by_cases h1 : p.1 < 1 <;> by_cases hθ : p.2 ∈ Ioo (-Real.pi) Real.pi <;>
        simp [Set.indicator,h0,h1,hθ,hd]
    · simp [Set.indicator,h0]
  rw [he,lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  change (∫⁻ p in Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * F (circlePoint p.1 p.2) ∂(volume.prod volume)) ≤ _
  rw [← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans_eq ?_
  apply lintegral_congr
  intro r
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma integrableOn_disk_of_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {B : ℝ → ℝ}
    (hB : IntegrableOn B (Ioo (0:ℝ) 1))
    (hBn : ∀ r ∈ Ioo (0:ℝ) 1, 0 ≤ B r)
    (hbound : ∀ r ∈ Ioo (0:ℝ) 1,
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤ ENNReal.ofReal (B r)) :
    IntegrableOn F disk := by
  refine ⟨hF.aestronglyMeasurable Metric.isOpen_ball.measurableSet,?_⟩
  have hn : ∀ᵐ z ∂(volume.restrict disk), 0 ≤ F z := ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet hFn
  apply (hasFiniteIntegral_iff_ofReal hn).mpr
  refine lt_of_le_of_lt (disk_lintegral_le_polar (fun z => ENNReal.ofReal (F z))) ?_
  refine lt_of_le_of_lt ?_ hB.hasFiniteIntegral
  apply setLIntegral_mono' measurableSet_Ioo
  intro r hr
  calc
    ENNReal.ofReal r * (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal r * ENNReal.ofReal (B r) := mul_le_mul le_rfl (hbound r hr) zero_le zero_le
    _ ≤ ENNReal.ofReal (B r) := by
      exact mul_le_of_le_one_left zero_le (by exact_mod_cast hr.2.le)
    _ = ‖B r‖ₑ := by rw [Real.enorm_eq_ofReal (hBn r hr)]

lemma circle_lintegral_eq {F : ℂ → ℝ} {r : ℝ}
    (hc : Continuous (fun θ : ℝ => F (circlePoint r θ)))
    (hn : ∀ θ, 0 ≤ F (circlePoint r θ)) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) =
      ENNReal.ofReal (∫ θ in -Real.pi..Real.pi, F (circlePoint r θ)) := by
  rw [restrict_Ioo_eq_restrict_Ioc]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall hn)).symm

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma continuousOn_deriv_univalent {f : ℂ → ℂ} (hf : UnivalentOn f disk) :
    ContinuousOn (deriv f) disk :=
  (hf.1.deriv Metric.isOpen_ball).continuousOn

lemma continuousOn_deriv_norm_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk) (t : ℝ) :
    ContinuousOn (fun z => ‖deriv f z‖^t) disk := by
  apply (continuousOn_deriv_univalent hf).norm.rpow_const
  intro z hz
  exact Or.inl (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf hz))

lemma integrableOn_boundary_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => (1-r)^a) (Ioo (0:ℝ) 1) := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := (1:ℝ)) ha).comp_sub_left 1
  have hi' : IntervalIntegrable (fun r : ℝ => (1-r)^a) volume 0 1 := by
    simpa using hi.symm
  exact hi'.1.mono_set Ioo_subset_Ioc_self

lemma integrableOn_disk_of_power_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {C a : ℝ} (hC : 0 ≤ C) (ha : -1 < a)
    (hbound : ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal (C*(1-r)^a)) :
    IntegrableOn F disk :=
  integrableOn_disk_of_circle_bound hF hFn ((integrableOn_boundary_rpow ha).const_mul C)
    (fun r hr => mul_nonneg hC (Real.rpow_nonneg (by linarith [hr.2]) _))
    (fun r hr => hbound r hr.1 hr.2)

lemma integrableOn_disk_boundary_power {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun z : ℂ => (1-‖z‖)^a) disk := by
  have hc : ContinuousOn (fun z : ℂ => (1-‖z‖)^a) disk := by
    apply (continuous_const.sub continuous_norm).continuousOn.rpow_const
    intro z hz
    exact Or.inl (ne_of_gt (by simpa [disk] using sub_pos.mpr (show ‖z‖ < 1 by simpa [disk] using hz)))
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt (by simpa [disk] using hz))) _) (C := 2*Real.pi)
    (by positivity) ha
  intro r hr hr1
  have he : (fun θ : ℝ => (1-‖circlePoint r θ‖)^a) = fun _ => (1-r)^a := by
    ext θ
    rw [circlePoint_norm,abs_of_pos hr]
  rw [circle_lintegral_eq (F := fun z => (1-‖z‖)^a) (r := r) (by rw [he]; exact continuous_const) (fun θ => Real.rpow_nonneg (by rw [circlePoint_norm,abs_of_pos hr]; linarith) _)]
  rw [he,intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  rw [show Real.pi + Real.pi = 2*Real.pi by ring]

lemma integrableOn_geometric_product {A B F : ℂ → ℝ} {s : Set ℂ} (hs : MeasurableSet s)
    (hA : IntegrableOn A s) (hB : IntegrableOn B s) (hF : AEStronglyMeasurable F (volume.restrict s))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hAn : ∀ z ∈ s, 0 ≤ A z) (hBn : ∀ z ∈ s, 0 ≤ B z)
    (hEq : ∀ z ∈ s, F z = A z^q * B z^(1-q)) : IntegrableOn F s := by
  apply ((hA.const_mul q).add (hB.const_mul (1-q))).mono' hF
  apply ae_restrict_of_forall_mem hs
  intro z hz
  rw [hEq z hz,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (hAn z hz) _) (Real.rpow_nonneg (hBn z hz) _))]
  exact Real.geom_mean_le_arith_mean2_weighted hq (by linarith) (hAn z hz) (hBn z hz) (by ring)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

end Brennan

end

end OAI
