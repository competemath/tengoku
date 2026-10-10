import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.ExpectedTransport

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma differentiableOn_classReciprocal (g : DiskClass) :
    DifferentiableOn ℂ (reciprocalDeriv (classFun g)) halfPlane :=
  fun _ hz => (hasDerivAt_reciprocalDeriv (classFun_schlicht g).1 hz).differentiableAt.differentiableWithinAt

lemma continuous_classReciprocal_eval :
    Continuous (fun p : DiskClass × halfPlane => reciprocalDeriv (classFun p.1) p.2) := by
  have hd : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
  exact hd.inv₀ (fun p => univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.2)

def reciprocalJet (n : ℕ) (g : DiskClass) : C(halfPlane,ℂ) :=
  ⟨fun z => iteratedDeriv n (reciprocalDeriv (classFun g)) z, continuousOn_iff_continuous_domRestrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_halfPlane (differentiableOn_classReciprocal g) n).continuousOn⟩

lemma continuous_reciprocalJet (n : ℕ) : Continuous (reciprocalJet n) := by
  have hc : Continuous (reciprocalJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_classReciprocal_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn (fun a => reciprocalDeriv (classFun a))
      (reciprocalDeriv (classFun g)) (𝓝 g) halfPlane :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_halfPlane h
      (Eventually.of_forall differentiableOn_classReciprocal) n)

lemma continuous_reciprocalJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × halfPlane => iteratedDeriv n (reciprocalDeriv (classFun p.1)) p.2) :=
  continuous_eval.comp ((continuous_reciprocalJet n).prodMap continuous_id)

lemma classReciprocal_at_I (g : DiskClass) : reciprocalDeriv (classFun g) Complex.I = 1 := by
  rw [reciprocalDeriv,(classFun_schlicht g).2.2,inv_one]

def normFirst (q d v : ℂ) : ℝ := 2*inner ℝ q (d*v)

def normSecond (q d e v : ℂ) : ℝ :=
  2*(inner ℝ (d*v) (d*v)+inner ℝ q ((e*v)*v))

lemma norm_first_one (d : ℂ) : normFirst 1 d 1 = 2*d.re := by
  simp [normFirst,Complex.inner]

lemma norm_first_I (d : ℂ) : normFirst 1 d Complex.I = -2*d.im := by
  simp [normFirst,Complex.inner]

lemma norm_second_laplacian (q d e : ℂ) :
    normSecond q d e 1+normSecond q d e Complex.I = 4*‖d‖^2 := by
  simp only [normSecond,mul_one]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  simp only [Complex.norm_mul,Complex.norm_I,mul_one]
  have he : (e*Complex.I)*Complex.I = -e := by rw [mul_assoc,Complex.I_mul_I,mul_neg_one]
  rw [he,inner_neg_right]
  ring

lemma continuous_normFirst : Continuous (fun p : ℂ × ℂ × ℂ => normFirst p.1 p.2.1 p.2.2) := by
  unfold normFirst
  fun_prop

lemma continuous_normSecond : Continuous (fun p : ℂ × ℂ × ℂ × ℂ => normSecond p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold normSecond
  fun_prop

def complexLine (v : ℂ) (t : ℝ) : ℂ := Complex.I+(t : ℂ)*v

def lineDomain (v : ℂ) : Set ℝ := {t | 0 < 1+t*v.im}

lemma isOpen_lineDomain (v : ℂ) : IsOpen (lineDomain v) :=
  isOpen_lt continuous_const (by fun_prop)

lemma complexLine_im (v : ℂ) (t : ℝ) : (complexLine v t).im = 1+t*v.im := by
  simp [complexLine,Complex.mul_im]

lemma complexLine_mem {v : ℂ} {t : ℝ} (ht : t ∈ lineDomain v) :
    0 < (complexLine v t).im := (complexLine_im v t).symm ▸ ht

@[simp] lemma complexLine_zero (v : ℂ) : complexLine v 0 = Complex.I := by simp [complexLine]
lemma zero_mem_lineDomain (v : ℂ) : (0 : ℝ) ∈ lineDomain v := by simp [lineDomain]

lemma class_logarithmicJet_I (g : DiskClass) :
    logarithmicJet (classFun g) Complex.I = Complex.I*deriv (reciprocalDeriv (classFun g)) Complex.I := by
  simp only [logarithmicJet,Complex.I_im,Complex.ofReal_one,mul_one,classReciprocal_at_I,div_one]

lemma continuous_root_logarithmicJet : Continuous (fun g : DiskClass => logarithmicJet (classFun g) Complex.I) := by
  simp_rw [class_logarithmicJet_I]
  have hc : Continuous (fun p : DiskClass × halfPlane => deriv (reciprocalDeriv (classFun p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_reciprocalJet_eval 1
  exact (hc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp [halfPlane]⟩ : halfPlane))))).const_mul _

end Brennan

end

end OAI
