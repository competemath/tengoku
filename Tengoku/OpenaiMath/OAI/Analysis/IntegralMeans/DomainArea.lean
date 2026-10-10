import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.PositiveArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

def normalizeDisk (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z-f 0)/deriv f 0

lemma normalizeDisk_hasDeriv {f : ℂ → ℂ} (hf : UnivalentOn f disk) {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt (normalizeDisk f) (deriv f z/deriv f 0) z :=
  ((hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const (f 0)).div_const _

lemma normalizeDisk_schlicht {f : ℂ → ℂ} (hf : UnivalentOn f disk) : Schlicht (normalizeDisk f) := by
  have h0 : (0:ℂ) ∈ disk := by simp [disk]
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf h0
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (normalizeDisk_hasDeriv hf hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    have hh : f z-f 0 = f w-f 0 := (div_left_inj' hn).mp he
    exact hf.2 hz hw (sub_left_inj.mp hh)
  · simp [normalizeDisk]
  · rw [(normalizeDisk_hasDeriv hf h0).deriv,div_self hn]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma univalent_inverse_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : UnivalentOn φ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (Function.invFunOn φ U) (deriv φ z)⁻¹ (φ z) := by
  have ha := hφ.1.analyticOnNhd hU z hz
  apply (ha.hasStrictDerivAt.to_local_left_inverse (univalent_deriv_ne_zero hU hφ hz) ?_).hasDerivAt
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hφ.2.leftInvOn_invFunOn hw

lemma bijOn_inverse_univalent {U V : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hb : BijOn φ U V) :
    UnivalentOn (Function.invFunOn φ U) V := by
  constructor
  · intro w hw
    obtain ⟨z,hz,rfl⟩ := hb.surjOn hw
    exact (univalent_inverse_hasDerivAt hU ⟨hφ,hb.injOn⟩ hz).differentiableAt.differentiableWithinAt
  · exact (Function.invFunOn_injOn_image φ U).mono hb.surjOn

lemma bijOn_inverse_image {U V : Set ℂ} {φ : ℂ → ℂ} (hb : BijOn φ U V) :
    Function.invFunOn φ U '' V = U := by
  rw [← hb.image_eq]
  exact hb.injOn.invFunOn_image (Subset.refl _)

lemma conformal_lintegral_eq {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, b w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
  have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
  dsimp only
  have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
  rw [hf,hd',abs_of_nonneg (sq_nonneg _)]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

end Brennan

end

end OAI
