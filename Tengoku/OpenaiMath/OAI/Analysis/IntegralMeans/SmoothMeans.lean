import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.TraceBounds

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

def logDisk (z : ℂ) : ℂ := Complex.exp (z*Complex.I)

lemma logDisk_norm (z : ℂ) : ‖logDisk z‖ = Real.exp (-z.im) := by
  simp [logDisk,Complex.norm_exp]

lemma logDisk_mem_disk {z : ℂ} (hz : 0 < z.im) : logDisk z ∈ disk := by
  simp only [disk,Metric.mem_ball,dist_zero_right,logDisk_norm]
  exact Real.exp_lt_one_iff.mpr (by linarith)

lemma logDisk_analytic (z : ℂ) : AnalyticAt ℂ logDisk z := by
  exact (analyticAt_cexp).comp ((analyticAt_id.mul analyticAt_const))

lemma logDisk_injOn : InjOn logDisk {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi} := by
  intro z hz w hw h
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hz.1 : -Real.pi < (z*Complex.I).im)
    (by simpa using hz.2.le : (z*Complex.I).im ≤ Real.pi)
    (by simpa using hw.1 : -Real.pi < (w*Complex.I).im)
    (by simpa using hw.2.le : (w*Complex.I).im ≤ Real.pi) h
  exact mul_right_cancel₀ Complex.I_ne_zero he

lemma logDisk_realProd (x y : ℝ) :
    logDisk (Complex.equivRealProdCLM.symm (x,y)) = circlePoint (Real.exp (-y)) x := by
  rw [logDisk,Complex.equivRealProdCLM_symm_apply]
  have he : ((x:ℂ)+y*Complex.I)*Complex.I = (-y:ℂ)+(x:ℂ)*Complex.I := by rw [add_mul,mul_assoc,Complex.I_mul_I]; ring
  rw [he,Complex.exp_add,← Complex.ofReal_neg,← Complex.ofReal_exp]
  rfl

lemma logDisk_periodic (z : ℂ) : logDisk (z+2*Real.pi) = logDisk z := by
  simp only [logDisk,add_mul,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma logStrip_smooth_periodic_side (H : ℂ → ℝ) (y : ℝ) :
    fderiv ℝ ((H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (-Real.pi,y) (1,0) =
      fderiv ℝ ((H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (Real.pi,y) (1,0) := by
  let g := (H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm
  have he : (fun p : ℝ × ℝ => g (p+(2*Real.pi,0))) = g := by
    ext p
    dsimp [g]
    have hz : Complex.equivRealProdCLM.symm ((p.1,p.2)+(2*Real.pi,0)) =
        Complex.equivRealProdCLM.symm p+2*Real.pi := by
      simp [Complex.equivRealProdCLM_symm_apply]
      ring
    rw [hz,logDisk_periodic]
  have hd := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0))
    (fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (-Real.pi,y)) (2*Real.pi,0))
  rw [he] at hd
  have hp : (-Real.pi,y)+(2*Real.pi,0) = (Real.pi,y) := by
    ext <;> dsimp <;> ring
  simpa only [hp] using hd

lemma exp_boundary_lower {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : y/2 ≤ 1-Real.exp (-y) := by
  have he := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  have hn : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [hn]
  have hi : (Real.exp y)⁻¹ ≤ (1+y)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hden : 0 < 1+y := by linarith
  have hf : y/2 ≤ 1-(1+y)⁻¹ := by
    rw [inv_eq_one_div]
    have hh : 1/(1+y) ≤ 1-y/2 := (div_le_iff₀ hden).mpr (by nlinarith)
    linarith
  linarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology
namespace Brennan

def bracketSq (z : ℂ) : ℝ := 1+z.re^2+z.im^2

def smoothPower (q : ℝ) (z : ℂ) : ℝ := bracketSq z ^ q

lemma bracketSq_eq (z : ℂ) : bracketSq z = 1+‖z‖^2 := by
  rw [Complex.sq_norm]
  simp [bracketSq,Complex.normSq_apply,pow_two,add_assoc]

lemma bracketSq_pos (z : ℂ) : 0 < bracketSq z := by rw [bracketSq_eq]; positivity

lemma bracketSq_contDiff (n : ℕ∞) : ContDiff ℝ n bracketSq := by
  exact (contDiff_const.add (Complex.reCLM.contDiff.pow 2)).add (Complex.imCLM.contDiff.pow 2)

lemma smoothPower_contDiff (q : ℝ) (n : ℕ∞) : ContDiff ℝ n (smoothPower q) :=
  (bracketSq_contDiff n).rpow_const_of_ne (fun z => (bracketSq_pos z).ne')

def bracketSqDeriv (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM

lemma bracketSq_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSq (bracketSqDeriv z) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).pow 2).const_add 1).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  convert! h using 1
  simp [bracketSqDeriv]

lemma smoothPower_hasFDerivAt (q : ℝ) (z : ℂ) :
    HasFDerivAt (smoothPower q) ((q*bracketSq z^(q-1)) • bracketSqDeriv z) z :=
  (bracketSq_hasFDerivAt z).rpow_const (Or.inl (bracketSq_pos z).ne')

lemma bracketSqDeriv_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSqDeriv
    ((ContinuousLinearMap.smulRight Complex.reCLM (2 • Complex.reCLM))+
      (ContinuousLinearMap.smulRight Complex.imCLM (2 • Complex.imCLM))) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.reCLM).add
    (((Complex.imCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.imCLM)
  convert! h using 1
  ext v w
  simp [ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

lemma smoothPower_secondReal (q : ℝ) (z u v : ℂ) :
    secondReal (smoothPower q) z u v =
      q*(q-1)*bracketSq z^(q-2)*(2*z.re*u.re+2*z.im*u.im)*(2*z.re*v.re+2*z.im*v.im)+
        q*bracketSq z^(q-1)*(2*u.re*v.re+2*u.im*v.im) := by
  have he : fderiv ℝ (smoothPower q) = fun z => (q*bracketSq z^(q-1)) • bracketSqDeriv z :=
    funext (fun z => (smoothPower_hasFDerivAt q z).fderiv)
  have hscalar := ((bracketSq_hasFDerivAt z).rpow_const (p := q-1) (Or.inl (bracketSq_pos z).ne')).const_mul q
  have hd := (hscalar.smul (bracketSqDeriv_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun z => (q*bracketSq z^(q-1)) • bracketSqDeriv z) z = _ at hd
  rw [secondReal,he,hd]
  simp [bracketSqDeriv,ContinuousLinearMap.smulRight_apply,smul_eq_mul,show q-1-1=q-2 by ring]
  ring

lemma laplacian_smoothPower (q : ℝ) (z : ℂ) :
    Laplacian.laplacian (smoothPower q) z =
      4*q*bracketSq z^(q-2)*(1+q*‖z‖^2) := by
  rw [laplacian_eq_secondReal,smoothPower_secondReal,smoothPower_secondReal]
  have he : bracketSq z^(q-1) = bracketSq z^(q-2)*bracketSq z := by
    simpa only [show q-2+1=q-1 by ring,Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q-2) 1
  rw [he,Complex.sq_norm]
  simp [Complex.normSq_apply,bracketSq]
  ring

lemma laplacian_smoothPower_bounds {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : ℂ) :
    0 ≤ Laplacian.laplacian (smoothPower q) z ∧
      Laplacian.laplacian (smoothPower q) z ≤ 4*q*bracketSq z^(q-1) := by
  have hz := bracketSq_pos z
  rw [laplacian_smoothPower]
  constructor
  · positivity
  · have he : bracketSq z^(q-1) = bracketSq z^(q-2)*bracketSq z := by
      simpa only [show q-2+1=q-1 by ring,Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q-2) 1
    rw [he,← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [bracketSq_eq]
    nlinarith [sq_nonneg ‖z‖]

lemma bracketSq_decay_integrable {q : ℝ} (hq : q < 1/4) :
    Integrable (fun z : ℂ => bracketSq z^(q-5/4)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 5/2-2*q)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma continuous_circle_smoothPower {f : ℂ → ℂ} (hf : Schlicht f) (q r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) : Continuous (fun θ => smoothPower q (f (circlePoint r θ))) := by
  apply (smoothPower_contDiff q 0).continuous.comp
  apply hf.1.1.continuousOn.comp_continuous (show Continuous (circlePoint r) from by unfold circlePoint; fun_prop)
  intro θ
  simpa only [disk,Metric.mem_ball,dist_zero_right,circlePoint_norm,abs_of_nonneg hr] using hr1

end Brennan

end

end OAI
