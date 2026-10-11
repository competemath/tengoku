import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.BrunnMinkowski

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

lemma quantile_first_moment {l r : ℝ} {f Q : ℝ → ℝ}
    (hQc : Continuous Q) (hQ0 : Q 0=l) (hQ1 : Q 1=r)
    (hQd : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt Q (f (Q s))⁻¹ s)
    (hfp : ∀ s ∈ Ioo (0:ℝ) 1, 0 < f (Q s)) :
    (∫ s in (0:ℝ)..1, Q s)=(∫ x in l..r, x*f x) := by
  have hdu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), HasDerivAt Q (f (Q s))⁻¹ s := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using hQd
  have hpu : ∀ s ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), 0 ≤ (f (Q s))⁻¹ := by
    simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using
      fun s hs => (inv_pos.mpr (hfp s hs)).le
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := fun x => x*f x) hQc.continuousOn hdu hpu
  rw [hQ0,hQ1] at he
  refine (intervalIntegral.integral_congr_ae_restrict ?_).trans he
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1),← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp [(hfp s hs).ne']

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_moment_indicator {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    (∫ x : E, K.indicator Prod.snd (x,s))=s*sliceDensity K s := by
  have he : (fun x : E => K.indicator Prod.snd (x,s)) =
      (horizontalSlice K s).indicator (fun _ => s) := by
    funext x
    by_cases hx : (x,s) ∈ K
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x ∈ horizontalSlice K s from hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x ∉ horizontalSlice K s from hx)]
  rw [he,integral_indicator (horizontalSlice_compact hK s).measurableSet,setIntegral_const]
  simp only [smul_eq_mul,sliceDensity,mul_comm]

lemma sliceDensity_moment_integrable {K : Set (E × ℝ)} (hK : IsCompact K) :
    Integrable (fun s => s*sliceDensity K s) := by
  have hi : Integrable (K.indicator Prod.snd) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (continuous_snd.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  exact hi.integral_prod_right.congr (Eventually.of_forall fun s => sliceDensity_moment_indicator hK s)

lemma sliceDensity_moment {K : Set (E × ℝ)} (hK : IsCompact K) :
    (∫ s, s*sliceDensity K s)=(∫ x in K, x.2) := by
  have hi : Integrable (K.indicator Prod.snd) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (continuous_snd.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have he := integral_prod_symm (K.indicator Prod.snd) hi
  simp_rw [sliceDensity_moment_indicator hK] at he
  rw [← he,← Measure.volume_eq_prod,integral_indicator hK.measurableSet]

lemma sliceDensity_interval_moment {K : Set (E × ℝ)} (hK : IsCompact K) {l r : ℝ}
    (hlr : l≤r) (hp : Prod.snd '' K ⊆ Icc l r) :
    (∫ s in l..r, s*sliceDensity K s)=(∫ x in K, x.2) := by
  rw [intervalIntegral.integral_of_le hlr,← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact sliceDensity_moment hK
  · intro s hs
    rw [sliceDensity_zero_of_notMem (fun h => hs (hp h)),mul_zero]

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere norm_coe)

/-- The unnormalized Euclidean first moment. It is the barycenter for unit
volume bodies, the only place where it is used below. -/
def firstMoment {n : ℕ} (K : Set (Space n)) : Space n := ∫ x in K, x

lemma shadowContinuousEquiv_inner {n : ℕ} (u : Sphere n)
    (z : perpendicular (u : Space n) × ℝ) :
    ⟪(u : Space n),shadowContinuousEquiv u z⟫=z.2 := by
  rw [shadowContinuousEquiv_apply,inner_add_right,perpendicular_inner,
    real_inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
  ring

lemma shadow_vertical_image {n : ℕ} (u : Sphere n) (K : Set (Space n)) :
    Prod.snd '' (shadowContinuousEquiv u ⁻¹' K)=(fun x => ⟪(u : Space n),x⟫) '' K := by
  ext s
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨shadowContinuousEquiv u z,hz,shadowContinuousEquiv_inner u z⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(shadowContinuousEquiv u).symm x,by simpa using hx,?_⟩
    rw [← shadowContinuousEquiv_inner u,ContinuousLinearEquiv.apply_symm_apply]

lemma shadow_firstMoment {n : ℕ} (u : Sphere n) {K : Set (Space n)} (hK : IsCompact K) :
    (∫ z in shadowContinuousEquiv u ⁻¹' K, z.2)=⟪(u : Space n),firstMoment K⟫ := by
  have he : MeasurePreserving (shadowContinuousEquiv u) := shadowMeasurableEquiv_measurePreserving u
  have hi := (he.restrict_preimage hK.measurableSet).integral_comp
    (shadowContinuousEquiv u).toHomeomorph.measurableEmbedding (fun x => ⟪(u : Space n),x⟫)
  simp_rw [shadowContinuousEquiv_inner] at hi
  rw [hi]
  exact integral_inner (continuous_id.continuousOn.integrableOn_compact hK) _

lemma perpendicular_finrank {n : ℕ} (u : Sphere n) :
    Module.finrank ℝ (perpendicular (u : Space n))=n-1 := by
  have hu : (u : Space n) ≠ 0 := by intro h; simpa [h] using norm_coe u
  have hr := (Submodule.span ℝ {(u : Space n)}).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu] at hr
  have he : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [he] at hr
  change Module.finrank ℝ ((Submodule.span ℝ {(u : Space n)})ᗮ)=n-1
  omega

lemma support_translate {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hKn : K.Nonempty) (c u : Space n) :
    support ((fun x => c+x) '' K) u=⟪u,c⟫+support K u := by
  apply le_antisymm
  · apply (support_le_iff (hK.image (by fun_prop)) (hKn.image _)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [inner_add_right]
    exact add_le_add_right (inner_le_support hK hx u) _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he,← inner_add_right]
    exact inner_le_support (hK.image (by fun_prop)) (mem_image_of_mem _ hx) u

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

def volumeRoot {n : ℕ} (K : Set (Space n)) : ℝ := (volume.real K)^((n:ℝ)⁻¹)

lemma volumeRoot_pos {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < volumeRoot K :=
  Real.rpow_pos_of_pos (volumeReal_pos_of_body hK hi) _

lemma volumeRoot_pow {n : ℕ} (hn : 0 < n) (K : Set (Space n)) :
    volumeRoot K^n=volume.real K :=
  Real.rpow_inv_natCast_pow measureReal_nonneg hn.ne'

lemma volumeRoot_smul {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (K : Set (Space n)) :
    volumeRoot (r • K)=r*volumeRoot K := by
  unfold volumeRoot
  rw [volumeReal_smul_nonneg hr]
  have hd : Module.finrank ℝ (Space n)=n := by simp [Space]
  rw [hd,Real.mul_rpow (pow_nonneg hr _) measureReal_nonneg,← Real.rpow_natCast,
    ← Real.rpow_mul hr, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),Real.rpow_one]

lemma interior_add_nonempty_left {n : ℕ} {K M : Set (Space n)}
    (hiK : (interior K).Nonempty) (hM : M.Nonempty) : (interior (K+M)).Nonempty := by
  obtain ⟨y,hy⟩ := hM
  obtain ⟨x,hx⟩ := hiK
  refine ⟨x+y,?_⟩
  exact (isOpen_interior.add_right.subset_interior_iff.mpr
    (add_subset_add interior_subset Subset.rfl)) (add_mem_add hx hy)

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

lemma minkowski_parameter_combo {n : ℕ} {K M : Set (Space n)}
    (hcK : Convex ℝ K) (hcM : Convex ℝ M) {s t a b : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • (K+s • M)+b • (K+t • M)=K+(a*s+b*t) • M := by
  rw [smul_add,smul_add,smul_smul,smul_smul,add_add_add_comm,
    ← hcK.add_smul ha hb,hab,one_smul,← hcM.add_smul (mul_nonneg ha hs) (mul_nonneg hb ht)]

lemma volumeRoot_diff_factor {n : ℕ} (hn : 0 < n) {K : Set (Space n)}
    (hv : 0 < volume.real K) :
    ((n:ℝ)*volumeRoot K^(n-1))*((n:ℝ)⁻¹*(volume.real K)^((n:ℝ)⁻¹-1))=1 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.rpow_sub hv,Real.rpow_one]
  change (n*volumeRoot K^(n-1))*((n:ℝ)⁻¹*(volumeRoot K/volume.real K))=1
  have hp : volumeRoot K^(n-1)*volumeRoot K=volume.real K := by
    rw [← pow_succ,Nat.sub_add_cancel hn,volumeRoot_pow hn]
  field_simp
  nlinarith [hp]

end PettyProjection
end

end OAI
