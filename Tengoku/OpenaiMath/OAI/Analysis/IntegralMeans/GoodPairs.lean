import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.BoundaryEscape

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

lemma compact_sublevels_iff_positive.{u_1} {X : Type u_1} [TopologicalSpace X] [T2Space X]
    {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔ ∀ r : ℝ, 0 < r → IsCompact {x | f x ≤ r} := by
  refine ⟨fun h r _ => h r,fun h r => ?_⟩
  exact (h (max r 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))).of_isClosed_subset
    (isClosed_le hf continuous_const) (fun x hx => (show f x ≤ r from hx).trans (le_max_left _ _))

lemma compact_positive_superlevels_iff {F : ℂ → ℂ} (k : ℝ) (ξ : ℂ)
    (hc : ContinuousOn F halfPlane) :
    (∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ)) ↔
      ∀ r : ℝ, IsCompact {z : halfPlane | ‖F z-ξ‖/z.val.im^k ≤ r} := by
  have hy (z : halfPlane) : 0 < z.val.im^k := Real.rpow_pos_of_pos z.property k
  have hcont : Continuous (fun z : halfPlane => ‖F z-ξ‖/z.val.im^k) := by
    refine ((hc.domRestrict.sub continuous_const).norm).div ?_ (fun z => ne_of_gt (hy z))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))
  rw [compact_sublevels_iff_positive hcont]
  have he (r : ℝ) (hr : 0 < r) :
      Subtype.val '' {z : halfPlane | ‖F z-ξ‖/z.val.im^k ≤ r} =
        closedPositiveSuperlevel F k (1/r) ξ := by
    ext z
    simp only [mem_image,mem_ofPred_eq,closedPositiveSuperlevel]
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      rw [div_le_iff₀ (hy w)] at hw
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hw
    · rintro ⟨hz,hzv⟩
      refine ⟨⟨z,hz⟩,?_,rfl⟩
      rw [div_le_iff₀ (hy ⟨z,hz⟩)]
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hzv
  constructor
  · intro h r hr
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [he r hr]
    exact h (1/r) (by positivity)
  · intro h δ hδ
    have hh := (h (1/δ) (by positivity)).image continuous_subtype_val
    rw [he (1/δ) (by positivity)] at hh
    simpa only [one_div_one_div] using hh

lemma ae_regular_values {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) :
    ∀ᵐ ξ ∂volume, ∀ z ∈ s, f z = ξ → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 := by
  let t : Set ℂ := {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap = 0}
  have hz : volume (f '' t) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z hz => (hf z hz.1).hasFDerivAt.hasFDerivWithinAt) (fun z hz => hz.2)
  filter_upwards [show ∀ᵐ ξ ∂volume, ξ ∉ f '' t from ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hz)] with ξ hξ z hzs hfz hdet
  exact hξ ⟨z,⟨hzs,hdet⟩,hfz⟩

lemma potential_superlevel_eq_closed {f : ℂ → ℂ} {k δ : ℝ} (hk : 0 ≤ k) (hδ : 0 < δ) (ξ : ℂ) :
    {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z} =
      closedPositiveSuperlevel f k δ ξ := by
  ext z
  by_cases hz : z ∈ halfPlane
  · simp only [mem_ofPred_eq,closedPositiveSuperlevel,show 0 < z.im from hz,hz,true_and]
    rw [potential_ge_iff_reciprocalPotential_le hk hδ hz,reciprocalPotential,
      div_le_iff₀ (Real.rpow_pos_of_pos hz k),inv_mul_eq_div]
  · simp only [mem_ofPred_eq,hz,false_and,closedPositiveSuperlevel]
    exact iff_false_intro (fun h => hz h.1) |>.symm

def pairingDomain (k : ℝ) : Set (DiskClass × halfPlane) :=
  {q | 0 < normalizedJacobian (classFun q.1) k q.2 ∧
    GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)}

end Brennan

end

end OAI
