import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Degree

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

lemma exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1) ∧ ∀ z, χ z ∈ Icc 0 1 := by
  obtain ⟨L,hL,hLc,hKL,hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,ℂ) hK.isClosed hKL (n := 2)
  have hs : tsupport (χ : ℂ → ℝ) ⊆ L := by
    apply closure_minimal _ hLc
    intro z hz
    by_contra hn
    exact hz (hχ0 z hn)
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,
    hL.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hLU,?_,hχrange⟩
  intro z hz
  exact hχ1.filter_mono (nhds_le_nhdsSet hz)

lemma det_fderiv_complex {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2 := by
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,determinant_complex_real,
    ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    Complex.I_mul, Complex.normSq_apply]
  ring

lemma smooth_extension_near_compact {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {x : ℂ → ℂ}
    (hx : ∀ z ∈ U, ContDiffAt ℝ 2 x z) :
    ∃ X : ℂ → ℂ, ContDiff ℝ 2 X ∧ ∀ z ∈ K, X =ᶠ[𝓝 z] x := by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩ := exists_smooth_cutoff hK hU hKU
  let X := fun z => (χ z : ℂ)*x z
  have hX : ContDiff ℝ 2 X := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hχc.contDiffAt).mul (hx z (hχU hz))
    · have he : X =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨X,hX,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [X,hw,Complex.ofReal_one,one_mul]

lemma det_holomorphic_plus_conjugate {h : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (a : ℝ) :
    LinearMap.det (fderiv ℝ (fun w => a • conj w+h w) z).toLinearMap =
      ‖deriv h z‖^2-a^2 := by
  have hD := (Complex.conjCLE.hasFDerivAt.const_smul a).add
    (hh.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun w => a • conj w+h w) _ z at hD
  rw [hD.fderiv,determinant_complex_real,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,add_apply,
    smul_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul,Complex.real_smul,Complex.normSq_apply]
  simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring

end Brennan

end

end OAI
