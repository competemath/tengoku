import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.BilinearEquality

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma smul_body {K : Set (Space n)} (hK : IsConvexBody K) {a : ℝ} (ha : a≠0) :
    IsConvexBody (a • K) := by
  refine ⟨hK.1.smul a,hK.2.1.smul a,?_⟩
  rw [interior_smul₀ ha]
  exact hK.2.2.image _

lemma translate_body {K : Set (Space n)} (hK : IsConvexBody K) (a : Space n) :
    IsConvexBody ((fun x => a+x) '' K) := by
  refine ⟨hK.1.image (by fun_prop),hK.2.1.translate a,?_⟩
  change (interior ((Homeomorph.addLeft a) '' K)).Nonempty
  rw [← (Homeomorph.addLeft a).image_interior]
  exact hK.2.2.image _

lemma isEllipsoid_linear_image {K : Set (Space n)} (hK : IsEllipsoid K)
    (T : Space n ≃ₗ[ℝ] Space n) : IsEllipsoid (T '' K) := by
  obtain ⟨a,S,rfl⟩ := hK
  refine ⟨T a,S.trans T,?_⟩
  simp only [image_image]
  congr 1
  funext x
  exact map_add T a (S x)

lemma isEllipsoid_translate {K : Set (Space n)} (hK : IsEllipsoid K) (b : Space n) :
    IsEllipsoid ((fun x => b+x) '' K) := by
  obtain ⟨a,T,rfl⟩ := hK
  refine ⟨b+a,T,?_⟩
  simp only [image_image]
  congr 1
  funext x
  exact (add_assoc b a (T x)).symm

lemma isEllipsoid_smul {K : Set (Space n)} (hK : IsEllipsoid K) {c : ℝ} (hc : c≠0) :
    IsEllipsoid (c • K) := by
  exact isEllipsoid_linear_image hK (LinearEquiv.smulOfNeZero ℝ (Space n) c hc)

lemma ellipsoid_homothety (T : Space n ≃L[ℝ] Space n) (a : Space n) {c : ℝ} (hc : c≠0) :
    IsEllipsoid ((fun x => a+c • x) '' (T '' unitBall n)) := by
  have he : IsEllipsoid (T '' unitBall n) := ⟨0,T.toLinearEquiv,by simp⟩
  have hh := isEllipsoid_translate (isEllipsoid_smul he hc) a
  change IsEllipsoid ((fun x => a+x) '' ((fun x => c • x) '' (T '' unitBall n))) at hh
  simpa only [image_image,Function.comp_def] using hh

def normalizeBody (K : Set (Space n)) : Set (Space n) := (normalizedVolume K)⁻¹ • K

lemma normalizeBody_body {K : Set (Space n)} (hK : IsConvexBody K) : IsConvexBody (normalizeBody K) :=
  smul_body hK (inv_ne_zero (normalizedVolume_pos hK.1 hK.2.2).ne')

lemma normalizeBody_nhds {K : Set (Space n)} (hK : IsCompact K) (h0 : K∈𝓝 (0:Space n)) :
    normalizeBody K∈𝓝 (0:Space n) := by
  apply (set_smul_mem_nhds_zero_iff (inv_ne_zero (normalizedVolume_pos hK ⟨0,mem_interior_iff_mem_nhds.mpr h0⟩).ne')).mpr h0

lemma normalizeBody_volume [NeZero n] {K : Set (Space n)} (hK : IsConvexBody K) : volume.real (normalizeBody K)=kappa n := by
  have hp := normalizedVolume_pos hK.1 hK.2.2
  rw [normalizeBody,volumeReal_smul_nonneg (inv_nonneg.mpr hp.le),finrank_euclideanSpace_fin,inv_pow,normalizedVolume_pow]
  field_simp [(volumeReal_pos_of_body hK.1 hK.2.2).ne',(kappa_pos n).ne']

lemma normalizeBody_ellipsoid {K : Set (Space n)} (hK : IsConvexBody K)
    (he : IsEllipsoid (normalizeBody K)) : IsEllipsoid K := by
  have hh := isEllipsoid_smul he (normalizedVolume_pos hK.1 hK.2.2).ne'
  simpa only [normalizeBody,smul_smul,mul_inv_cancel₀ (normalizedVolume_pos hK.1 hK.2.2).ne',one_smul] using hh

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma measurePair_comm {μ ν : Measure (Space n)} [SFinite μ] [SFinite ν]
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hν : Integrable (fun x : Space n => ‖x‖) ν) : measurePair μ ν=measurePair ν μ := by
  have hi : Integrable (fun z : Space n × Space n => |⟪z.1,z.2⟫|) (μ.prod ν) := by
    apply (hμ.mul_prod hν).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_abs] using abs_real_inner_le_norm z.1 z.2)
  rw [measurePair,integral_integral_swap hi]
  unfold measurePair
  simp_rw [real_inner_comm]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma volumeReal_translate (K : Set (Space n)) (a : Space n) :
    volume.real ((fun x => a+x) '' K)=volume.real K := by
  unfold Measure.real
  rw [image_add_left,measure_preimage_add]

lemma normalizedVolume_translate (K : Set (Space n)) (a : Space n) :
    normalizedVolume ((fun x => a+x) '' K)=normalizedVolume K := by
  rw [normalizedVolume_formula,volumeReal_translate,← normalizedVolume_formula]

lemma shadowVolume_translate (K : Set (Space n)) (a u : Space n) :
    shadowVolume ((fun x => a+x) '' K) u=shadowVolume K u := by
  have he : (perpendicular u).orthogonalProjectionOnto '' ((fun x => a+x) '' K)=
      (fun z => (perpendicular u).orthogonalProjectionOnto a+z) ''
        ((perpendicular u).orthogonalProjectionOnto '' K) := by
    simp only [image_image]
    congr 1
    funext x
    exact map_add _ a x
  unfold shadowVolume Measure.real
  rw [he,image_add_left,measure_preimage_add]

lemma projectionBody_translate (K : Set (Space n)) (a : Space n) :
    projectionBody ((fun x => a+x) '' K)=projectionBody K := by
  ext x
  simp only [projectionBody,mem_ofPred_eq,shadowVolume_translate]

lemma projectionRatio_translate (K : Set (Space n)) (a : Space n) :
    projectionRatio ((fun x => a+x) '' K)=projectionRatio K := by
  rw [projectionRatio,projectionBody_translate,volumeReal_translate,projectionRatio]

lemma shadowVolume_smul (K : Set (Space n)) {a : ℝ} (ha : 0≤ a) (u : Spherical.Sphere n) :
    shadowVolume (a • K) u=a^(n-1)*shadowVolume K u := by
  have he : (perpendicular (u:Space n)).orthogonalProjectionOnto '' (a • K)=
      a • ((perpendicular (u:Space n)).orthogonalProjectionOnto '' K) := by
    change _ '' ((fun x : Space n => a • x) '' K)=
      (fun z : perpendicular (u:Space n) => a • z) '' (_ '' K)
    simp only [image_image]
    congr 1
    funext x
    exact map_smul _ a x
  unfold shadowVolume
  rw [he,volumeReal_smul_nonneg ha,perpendicular_finrank]

lemma projectionBody_smul (K : Set (Space n)) {a : ℝ} (ha : 0< a) :
    projectionBody (a • K)=a^(n-1) • projectionBody K := by
  have hp : 0< a^(n-1) := pow_pos ha _
  ext x
  rw [mem_smul_set_iff_inv_smul_mem₀ hp.ne']
  change (∀ u : Space n,‖u‖=1 → ⟪u,x⟫≤ shadowVolume (a • K) u) ↔
    (∀ u : Space n,‖u‖=1 → ⟪u,(a^(n-1))⁻¹ • x⟫≤ shadowVolume K u)
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  have hv := shadowVolume_smul K ha.le (⟨u,by simpa only [mem_sphere,dist_zero_right] using hu⟩ : Spherical.Sphere n)
  change shadowVolume (a • K) u=a^(n-1)*shadowVolume K u at hv
  rw [hv,inner_smul_right]
  rw [show (a^(n-1))⁻¹*⟪u,x⟫=⟪u,x⟫/(a^(n-1)) by ring,div_le_iff₀ hp]
  rw [mul_comm (a^(n-1))]

lemma projectionRatio_smul (K : Set (Space n))
    {a : ℝ} (ha : 0< a) : projectionRatio (a • K)=projectionRatio K := by
  rw [projectionRatio,projectionBody_smul K ha,volumeReal_smul_nonneg (pow_nonneg ha.le _),
    volumeReal_smul_nonneg ha.le,finrank_euclideanSpace_fin,projectionRatio,mul_pow]
  have he : (a^(n-1))^n=(a^n)^(n-1) := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [he]
  field_simp [ha.ne']

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
variable {n : ℕ}

lemma projectionRatio_normalized {n : ℕ} (hn : 2≤n) [NeZero n] {K : Set (Space n)}
    (hv : volume.real K=kappa n) :
    projectionRatio K=normalizedVolume (projectionBody K)^n*kappa n^(2-(n:ℤ)) := by
  have hn1 : n-1=(n-2)+1 := by omega
  have hn2 : (2-(n:ℤ))=-((n-2:ℕ):ℤ) := by omega
  have hvP : volume.real (projectionBody K)=normalizedVolume (projectionBody K)^n*kappa n := by
    exact (div_eq_iff (kappa_pos n).ne').mp (normalizedVolume_pow (projectionBody K)).symm
  rw [projectionRatio,hv,hvP,hn1,pow_succ,hn2,zpow_neg,zpow_natCast]
  field_simp [(kappa_pos n).ne']

end PettyProjection
end

end OAI
