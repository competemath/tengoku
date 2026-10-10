import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Moments

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

def circlePoint (r θ : ℝ) : ℂ := (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)

def arcInterval : Set ℝ := Icc (-Real.pi/4) (Real.pi/4)

def arcD (r θ : ℝ) : ℝ := 1+2*r*Real.cos θ+r^2

def arcX (r θ : ℝ) : ℝ := 2*r*Real.sin θ/arcD r θ

def arcY (r θ : ℝ) : ℝ := (1-r^2)/arcD r θ

def arcXDeriv (r θ : ℝ) : ℝ := (4*r^2+2*r*(1+r^2)*Real.cos θ)/(arcD r θ)^2

lemma arc_cos_nonneg {θ : ℝ} (hθ : θ ∈ arcInterval) : 0 ≤ Real.cos θ := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> have hp := Real.pi_pos <;> dsimp [arcInterval] at hθ <;> linarith [hθ.1,hθ.2]

lemma arcD_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1 ≤ arcD r θ ∧ arcD r θ ≤ (1+r)^2 ∧ arcD r θ ≤ 4 := by
  have hc := arc_cos_nonneg hθ
  have hc1 := Real.cos_le_one θ
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 0 ≤ 2*r := by positivity
  dsimp [arcD]
  have hm := mul_nonneg hr2 hc
  have hm1 := mul_le_mul_of_nonneg_left hc1 hr2
  constructor
  · nlinarith [sq_nonneg r]
  constructor <;> nlinarith

lemma arcX_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    arcX r θ ∈ Icc (-1) 1 := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  have hs := Real.neg_one_le_sin θ
  have hs1 := Real.sin_le_one θ
  have h2r : 0 ≤ 2*r := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hs h2r
  have hm2 := mul_le_mul_of_nonneg_left hs1 h2r
  have hD2 : 2*r ≤ arcD r θ := by
    dsimp [arcD]
    nlinarith [mul_nonneg h2r hc,sq_nonneg (r-1)]
  constructor
  · exact (le_div_iff₀ hD).mpr (by nlinarith)
  · exact (div_le_iff₀ hD).mpr (by nlinarith)

lemma arcY_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    (1-r)/2 ≤ arcY r θ ∧ arcY r θ ≤ 2*(1-r) := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hr0 : 0 ≤ r := by linarith
  have hd0 : 0 ≤ 1-r := by linarith
  constructor
  · apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ (1-r)/2)
    have hb : (1-r)/2*(1+r)^2 ≤ 1-r^2 := by nlinarith [mul_nonneg hd0 (sq_nonneg (1+r))]
    exact h.trans hb
  · apply (div_le_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.1 (by positivity : 0 ≤ 2*(1-r))
    nlinarith [sq_nonneg (r-1)]

lemma arcX_hasDerivAt {r θ : ℝ} (hD : arcD r θ ≠ 0) :
    HasDerivAt (arcX r) (arcXDeriv r θ) θ := by
  have hn := (Real.hasDerivAt_sin θ).const_mul (2*r)
  have hd := (((Real.hasDerivAt_cos θ).const_mul (2*r)).const_add 1).add_const (r^2)
  have h := hn.div hd hD
  change HasDerivAt (arcX r) _ θ at h
  have he : arcXDeriv r θ =
      (2*r*Real.cos θ*arcD r θ-2*r*Real.sin θ*(2*r * -Real.sin θ))/(arcD r θ)^2 := by
    unfold arcXDeriv arcD
    congr 1
    have hc := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg r]
  rw [he]
  exact h

lemma arcXDeriv_lower {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1/16 ≤ arcXDeriv r θ := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  dsimp only [arcXDeriv]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hm : 0 ≤ 2*r*(1+r^2)*Real.cos θ := mul_nonneg (by positivity) hc
  have hsq : (arcD r θ)^2 ≤ 16 := by nlinarith [hd.2.2]
  nlinarith [sq_nonneg (r-1/2)]

lemma continuousOn_arcXDeriv {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) :
    ContinuousOn (arcXDeriv r) arcInterval := by
  apply ContinuousOn.div
  · fun_prop
  · unfold arcD
    fun_prop
  · intro θ hθ
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))

lemma arcX_monotone {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) : MonotoneOn (arcX r) arcInterval := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))).continuousAt.continuousWithinAt
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 (interior_subset hθ)).1))).hasDerivWithinAt
  · intro θ hθ
    exact le_trans (by norm_num) (arcXDeriv_lower hr hr1 (interior_subset hθ))

lemma circlePoint_norm (r θ : ℝ) : ‖circlePoint r θ‖ = |r| := by
  simp [circlePoint,Complex.norm_exp]

lemma circlePoint_re (r θ : ℝ) : (circlePoint r θ).re = r*Real.cos θ := by
  simp [circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma circlePoint_im (r θ : ℝ) : (circlePoint r θ).im = r*Real.sin θ := by
  simp [circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma one_add_circlePoint_norm_sq (r θ : ℝ) : ‖1+circlePoint r θ‖^2 = arcD r θ := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,circlePoint_re,circlePoint_im,zero_add]
  dsimp [arcD]
  nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg r]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : circlePoint r θ ∈ disk := by
  simpa [disk,circlePoint_norm,abs_of_nonneg hr] using hr1

lemma neg_circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : -circlePoint r θ ∈ disk := by
  simpa only [disk,Metric.mem_ball,dist_zero_right,norm_neg] using circlePoint_mem_disk hr hr1 θ

lemma halfCayley_re (z : ℂ) : (halfCayley z).re = -2*z.im/‖1-z‖^2 := by
  simp only [halfCayley,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma halfCayley_neg_circlePoint {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    halfCayley (-circlePoint r θ) = (arcX r θ:ℂ)+(arcY r θ:ℂ)*Complex.I := by
  have hz := neg_circlePoint_mem_disk hr hr1 θ
  apply Complex.ext
  · rw [halfCayley_re]
    simp only [Complex.neg_im,circlePoint_im,sub_neg_eq_add,one_add_circlePoint_norm_sq,
      Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im]
    dsimp [arcX]
    ring
  · rw [halfCayley_im hz]
    simp only [norm_neg,circlePoint_norm,abs_of_nonneg hr,sub_neg_eq_add,one_add_circlePoint_norm_sq,
      Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.ofReal_re,Complex.I_im]
    simp [arcY]

lemma inverse_deriv_square_conversion {f : ℂ → ℂ} (hf : Schlicht f) {w : ℂ} (hw : w ∈ disk) :
    ‖deriv f w‖^(-2:ℝ) ≤ 16*classWeight (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf))
      ⟨halfCayley w,halfCayley_maps hw⟩ := by
  let g := classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)
  let z : halfPlane := ⟨halfCayley w,halfCayley_maps hw⟩
  have he := (classFun_classOfHalf (diskToHalf_schlicht hf)).deriv isOpen_halfPlane z.2
  have hfhe : EqOn (halfToDisk (diskToHalf f)) f disk := fun _ hz => halfToDisk_diskToHalf hz
  have hd := (hasDerivAt_halfToDisk (diskToHalf_schlicht hf).1.1 hw).deriv
  rw [hfhe.deriv Metric.isOpen_ball hw] at hd
  have hw1 : ‖w‖ < 1 := by simpa [disk] using hw
  have hb : ‖1-w‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1+‖w‖ ≤ 2 by linarith))
  have ha : 0 < ‖deriv (diskToHalf f) (halfCayley w)‖ := norm_pos_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (diskToHalf_schlicht hf).1 z.2)
  rw [hd,norm_div,norm_pow,Real.rpow_neg (by positivity),Real.rpow_two]
  unfold classWeight
  change _ ≤ 16*‖reciprocalDeriv (classFun g) z‖^2
  rw [reciprocalDeriv,he,norm_inv]
  have hb4 : ‖1-w‖^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) hb _
  have hz0 : ‖1-w‖ ≠ 0 := norm_ne_zero_iff.mpr (halfCayley_den_ne_zero hw)
  dsimp only [z]
  field_simp [ha.ne',hz0]
  nlinarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

attribute [local irreducible] classFun classWeight rerootClass

lemma continuous_horizontalWeight (g : DiskClass) (v : ℝ) (hv : 0 < v) :
    Continuous (fun x => classWeight g (halfPoint x v hv)) :=
  continuous_classWeight.comp (continuous_const.prodMk
    (continuous_halfPoint continuous_id continuous_const (fun _ => hv)))

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  fun_prop

lemma continuous_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (circlePoint r θ)‖^t) := by
  have hc : Continuous (fun θ => deriv f (circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r)
      (circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero Metric.isOpen_ball hf (circlePoint_mem_disk hr hr1 θ))))

lemma continuous_neg_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (-circlePoint r θ)‖^t) := by
  have hc : Continuous (fun θ => deriv f (-circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r).neg
      (neg_circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero Metric.isOpen_ball hf (neg_circlePoint_mem_disk hr hr1 θ))))

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

def rotateDisk (f : ℂ → ℂ) (α z : ℂ) : ℂ := f (α*z)/α

lemma rotateDisk_maps {α : ℂ} (hα : ‖α‖ = 1) : MapsTo (fun z => α*z) disk disk := by
  intro z hz
  simpa [disk,norm_mul,hα] using hz

lemma rotateDisk_hasDerivAt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    {α z : ℂ} (hα : ‖α‖ = 1) (hz : z ∈ disk) :
    HasDerivAt (rotateDisk f α) (deriv f (α*z)) z := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  have hd := ((hf _ (rotateDisk_maps hα hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (rotateDisk_maps hα hz))).hasDerivAt
  convert (hd.comp z ((hasDerivAt_id z).const_mul α)).div_const α using 1 <;> try rfl
  simp [hα0]

lemma rotateDisk_schlicht {f : ℂ → ℂ} (hf : Schlicht f) {α : ℂ} (hα : ‖α‖ = 1) :
    Schlicht (rotateDisk f α) := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  refine ⟨⟨fun z hz => (rotateDisk_hasDerivAt hf.1.1 hα hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    exact mul_left_cancel₀ hα0 (hf.1.2 (rotateDisk_maps hα hz) (rotateDisk_maps hα hw)
      ((div_left_inj' hα0).mp he))
  · simp [rotateDisk,hf.2.1]
  · rw [(rotateDisk_hasDerivAt hf.1.1 hα (show (0:ℂ) ∈ disk by simp [disk])).deriv]
    simpa using hf.2.2

lemma circlePoint_shift (r θ c : ℝ) :
    (-Complex.exp ((c:ℂ)*Complex.I))*(-circlePoint r θ) = circlePoint r (θ+c) := by
  simp only [circlePoint,Complex.ofReal_add,add_mul,Complex.exp_add,neg_mul_neg]
  ring

lemma periodic_circlePoint (r : ℝ) : Periodic (circlePoint r) (2*Real.pi) := by
  simpa [circlePoint,circleMap] using periodic_circleMap (0:ℂ) r

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma dyadic_growth_compare {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) {n : ℕ}
    (hn : δ ≤ 2*(1/2:ℝ)^n) :
    ((2:ℝ)^a)^n ≤ (2:ℝ)^a * δ^(-a) := by
  have hv : 0 < (1/2:ℝ)^n := by positivity
  have he : ((2:ℝ)^a)^n = ((1/2:ℝ)^n)^(-a) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),← Real.rpow_natCast (1/2:ℝ),
      ← Real.rpow_mul (by norm_num)]
    rw [show (1/2:ℝ) = 2^(-1:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [he]
  have hb := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ/2)
    (show δ/2 ≤ (1/2:ℝ)^n by linarith) (neg_nonpos.mpr ha)
  refine hb.trans_eq ?_
  rw [Real.div_rpow hδ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul,mul_comm]

end Brennan

end

end OAI
