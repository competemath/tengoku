import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.AffinePosition

namespace OAI

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeMoment)
namespace RelativeGauge
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}

omit [NeZero n] in
lemma scale_momentField (g : RelativeGauge (⊤ : Submodule ℝ (Space n)))
    {a : ℝ} (ha : 0<a) (k : ℕ) :
    Position.momentField (g.scale a ha).toSeminorm k=Position.momentField g.toSeminorm k := by
  apply WithLp.ofLp_injective
  funext ij
  change mean (fun u : Sphere n => (a*g u)^k*(u:Space n) ij.1*(u:Space n) ij.2)/
    mean (fun u : Sphere n => (a*g u)^k)-_=mean (fun u : Sphere n => g u^k*(u:Space n) ij.1*(u:Space n) ij.2)/
    mean (fun u : Sphere n => g u^k)-_
  have he : mean (fun u : Sphere n => (a*g u)^k*(u:Space n) ij.1*(u:Space n) ij.2)=
      a^k*mean (fun u : Sphere n => g u^k*(u:Space n) ij.1*(u:Space n) ij.2) := by
    simp_rw [mul_pow,mul_assoc]
    exact integral_const_mul _ _
  have he' : mean (fun u : Sphere n => (a*g u)^k)=a^k*mean (fun u : Sphere n => g u^k) := by
    simp only [mul_pow,mean,integral_const_mul]
  rw [he,he',mul_div_mul_left _ _ (pow_ne_zero _ ha.ne')]

lemma volumeNormalize_harmonic (hn : 2≤n) (g : RelativeGauge (⊤ : Submodule ℝ (Space n)))
    (hF : Position.momentField g.toSeminorm (Scalar.exponent n)=0) :
    (Spherical.harmonicSpace n 2).starProjection (Spherical.toH n
      (Spherical.restrictContinuous (fun x => g.volumeNormalize x^Scalar.exponent n)
        ((Spherical.seminorm_continuous n g.volumeNormalize.toSeminorm).pow _)))=0 := by
  apply Position.field_zero_harmonic hn _ (g.volumeNormalize.ne_zero top_ne_bot)
  rw [volumeNormalize,g.scale_momentField,hF]

lemma volumeNormalize_representation
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0<cosineSeminorm μ hμ x)
    (g : RelativeGauge (⊤ : Submodule ℝ (Space n))) (hg : IsMinimizer μ (regime n) g) :
    ∃ s : ℝ,0<s ∧ Represents μ g.volumeNormalize.toSeminorm (Scalar.exponent n) s ∧
      supportFunctional μ g.volumeNormalize.body=s*gaugeMoment g.volumeNormalize.toSeminorm (Scalar.exponent n-1) := by
  have hm := Position.mean_power_pos g.volumeNormalize.toSeminorm (g.volumeNormalize.ne_zero top_ne_bot) (Scalar.exponent n-1)
  have hv := normalizedVolume_pos g.compact g.top_interior
  have hf : 0<supportFunctional μ g.volumeNormalize.body := by
    rw [volumeNormalize,g.functional_scale,hg.1,mul_one]
    exact inv_pos.mpr hv
  refine ⟨_,div_pos hf hm,scaled_represents hμ hq g hg.1 hg.2 hv,?_⟩
  exact (div_mul_cancel₀ _ hm.ne').symm

end RelativeGauge
end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere mean sigma gaugeMoment cosineConstant)
open RelativeGauge

lemma normalizedVolume_of_volume {n : ℕ} {K : Set (Space n)} (hK : volume.real K=kappa n) :
    normalizedVolume K=1 := by
  rw [normalizedVolume_formula,hK,div_self (kappa_pos n).ne',Real.one_rpow]

lemma cosine_equiv_pos {n : ℕ} {μ : Measure (Space n)}
    (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x)
    (T : Space n ≃L[ℝ] Space n) :
    ∀ x : Space n,x≠0 → 0< cosineSeminorm (μ.map T) (norm_integrable_map hμ T.toContinuousLinearMap) x := by
  intro x hx
  exact cosine_map_pos hμ hq T.toContinuousLinearMap x ⟨T.symm x,T.apply_symm_apply x⟩ hx

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise
namespace PettyProjection
open Spherical (Sphere norm_coe seminorm_continuous)
variable {n : ℕ} [NeZero n] {K : Set (Space n)}

lemma gaugeMeasure_norm_integrable (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : K∈𝓝 (0:Space n)) : Integrable (fun x : Space n => ‖x‖) (gaugeProjectionMeasure K) := by
  let := gaugeMeasure_finite hK hc h0
  exact boundedMeasure_integrable_continuous (gaugeMeasure_bounded hc h0) continuous_norm

lemma gaugeMeasure_cosine_pos (hK : IsCompact K) (hc : Convex ℝ K)
    (h0 : K∈𝓝 (0:Space n)) :
    ∀ x : Space n,x≠0 → 0< cosineSeminorm (gaugeProjectionMeasure K) (gaugeMeasure_norm_integrable hK hc h0) x := by
  intro x hx
  let u : Sphere n := ⟨‖x‖⁻¹ • x,by simp [norm_smul,hx]⟩
  have hu := gaugeMeasure_shadow hK hc h0 u
  have hh := shadowVolume_pos hK h0 (u:Space n)
  have hn : 0 < (n:ℝ)*kappa n := mul_pos (Nat.cast_pos.mpr (NeZero.pos n)) (kappa_pos n)
  have hp : 0< cosineSeminorm (gaugeProjectionMeasure K) (gaugeMeasure_norm_integrable hK hc h0) u := by
    change 0 < ∫ y,|⟪y,(u:Space n)⟫| ∂gaugeProjectionMeasure K
    nlinarith
  change 0< cosineSeminorm _ _ (‖x‖⁻¹ • x) at hp
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hp
  exact (mul_pos_iff.mp hp).elim (fun h => h.2) (fun h => False.elim (not_lt_of_ge (inv_nonneg.mpr (norm_nonneg x)) h.1))

def projectionSeminorm (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) : Seminorm ℝ (Space n) := by
  let q := cosineSeminorm (gaugeProjectionMeasure K) (gaugeMeasure_norm_integrable hK hc h0)
  let c : ℝ := (n : ℝ)*kappa n/2
  have hc : 0 ≤ c := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (kappa_pos n).le) (by norm_num)
  exact Seminorm.of (fun x => c*q x)
    (fun x y => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (map_add_le_add q x y) hc)
    (fun r x => by rw [map_smul_eq_mul];ring)

lemma projectionSeminorm_unit (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (u : Sphere n) : projectionSeminorm hK hc h0 u=shadowVolume K u := by
  have hh := gaugeMeasure_shadow hK hc h0 u
  change (n*kappa n/2)*(∫ x,|⟪x,(u:Space n)⟫| ∂gaugeProjectionMeasure K)=_
  linarith

lemma projectionSeminorm_pos (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (u : Sphere n) : 0< projectionSeminorm hK hc h0 u := by
  rw [projectionSeminorm_unit]
  exact shadowVolume_pos hK h0 u

lemma projectionBody_eq_wulff (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionBody K=wulff (fun u : Sphere n => projectionSeminorm hK hc h0 u) := by
  ext x
  constructor
  · intro hx u
    change ⟪(u:Space n),x⟫ ≤ projectionSeminorm hK hc h0 u
    rw [projectionSeminorm_unit]
    exact hx u (norm_coe u)
  · intro hx u hu
    let v : Sphere n := ⟨u,by simpa only [mem_sphere,dist_zero_right] using hu⟩
    have h : ⟪u,x⟫ ≤ projectionSeminorm hK hc h0 v := hx v
    rw [projectionSeminorm_unit] at h
    exact h

lemma projectionBody_body (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    IsConvexBody (projectionBody K) := by
  rw [projectionBody_eq_wulff hK hc h0]
  exact wulff_body ⟨fun u : Sphere n => projectionSeminorm hK hc h0 (u:Space n),(seminorm_continuous n (projectionSeminorm hK hc h0)).comp continuous_subtype_val⟩
    (projectionSeminorm_pos hK hc h0)

lemma projectionBody_nhds (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n)) :
    projectionBody K∈𝓝 (0:Space n) := by
  rw [projectionBody_eq_wulff hK hc h0]
  exact wulff_nhds ⟨fun u : Sphere n => projectionSeminorm hK hc h0 (u:Space n),(seminorm_continuous n (projectionSeminorm hK hc h0)).comp continuous_subtype_val⟩
    (projectionSeminorm_pos hK hc h0)

lemma projectionBody_support (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (x : Space n) : support (projectionBody K) x=
      (n*kappa n/2)*∫ y,|⟪y,x⟫| ∂gaugeProjectionMeasure K := by
  rw [projectionBody_eq_wulff hK hc h0,support_wulff_seminorm _ (projectionSeminorm_pos hK hc h0)]
  rfl

lemma projectionBody_support_unit (hK : IsCompact K) (hc : Convex ℝ K) (h0 : K∈𝓝 (0:Space n))
    (u : Sphere n) : support (projectionBody K) u=shadowVolume K u := by
  rw [projectionBody_eq_wulff hK hc h0,support_wulff_seminorm _ (projectionSeminorm_pos hK hc h0),
    projectionSeminorm_unit]

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped NNReal RealInnerProductSpace Pointwise Gradient
namespace PettyProjection
open Spherical (Sphere norm_coe mean)
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma unitBall_body : IsConvexBody (unitBall n) := by
  exact ⟨isCompact_closedBall _ _,convex_closedBall _ _,⟨0,mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ (by norm_num))⟩⟩

omit [NeZero n] in
lemma unitBall_nhds : unitBall n∈𝓝 (0:Space n) := closedBall_mem_nhds _ (by norm_num)

omit [NeZero n] in
lemma shadowVolume_unitBall (u : Sphere n) : shadowVolume (unitBall n) u=kappa (n-1) := by
  have him : (perpendicular (u:Space n)).orthogonalProjectionOnto '' unitBall n=
      closedBall (0:perpendicular (u:Space n)) 1 := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simp only [unitBall,mem_closedBall,dist_zero_right] at hx ⊢
      exact ((perpendicular (u:Space n)).norm_orthogonalProjectionOnto_apply_le x).trans hx
    · intro hz
      refine ⟨z,?_,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z⟩
      simpa [unitBall] using hz
  let e : perpendicular (u:Space n) ≃ₗᵢ[ℝ] Space (n-1) :=
    ((stdOrthonormalBasis ℝ (perpendicular (u:Space n))).reindex (finCongr (perpendicular_finrank u))).repr
  unfold shadowVolume
  rw [him]
  have he : e ⁻¹' unitBall (n-1)=closedBall (0:perpendicular (u:Space n)) 1 := by
    ext z
    simp [unitBall,dist_zero_right]
  have hh := e.measurePreserving.measure_preimage (isClosed_closedBall.measurableSet.nullMeasurableSet : NullMeasurableSet (unitBall (n-1)) volume)
  change volume (e ⁻¹' unitBall (n-1)) = volume (unitBall (n-1)) at hh
  rw [he] at hh
  exact congrArg ENNReal.toReal hh

omit [NeZero n] in
lemma gradient_norm_unit (u : Sphere n) : ∇ (fun x : Space n => ‖x‖) (u:Space n)=(u:Space n) := by
  have hd := (hasStrictFDerivAt_norm_sq (u:Space n)).hasFDerivAt.sqrt (by rw [norm_coe];norm_num)
  simp only [norm_coe,one_pow,Real.sqrt_one,mul_one] at hd
  have hs : (1/(2:ℝ)) • (2 • innerSL ℝ (u:Space n))=innerSL ℝ (u:Space n) := by
    ext v
    simp only [smul_apply,two_smul,smul_eq_mul,add_apply]
    ring
  rw [hs] at hd
  have hd' : HasFDerivAt (fun x : Space n => ‖x‖) (innerSL ℝ (u:Space n)) (u:Space n) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hd
  apply (InnerProductSpace.toDual ℝ (Space n)).injective
  rw [toDual_gradient,hd'.fderiv]
  rfl

lemma ball_cosine_constant : 2*kappa (n-1)=(n:ℝ)*kappa n*Spherical.cosineConstant n := by
  let u : Sphere n := Spherical.pole n
  have hh := shadow_gauge_formula (K :=unitBall n) unitBall_body.1 unitBall_body.2.1 unitBall_nhds u
  have hg : gauge (unitBall n)=(fun x : Space n => ‖x‖) := by
    funext x
    simp [unitBall,gauge_closedBall (E :=Space n) (by norm_num : (0:ℝ)≤1) x]
  have he : (fun v : Sphere n => (gauge (unitBall n) (v:Space n))⁻¹^n*
      |⟪∇ (gauge (unitBall n)) (v:Space n),(u:Space n)⟫|)=
      (fun v : Sphere n => |⟪(u:Space n),(v:Space n)⟫|) := by
    funext v
    rw [hg,gradient_norm_unit]
    change (‖(v:Space n)‖)⁻¹^n*|⟪(v:Space n),(u:Space n)⟫|=_
    rw [norm_coe]
    simp only [inv_one,one_pow,one_mul,real_inner_comm (v:Space n)]
  rw [shadowVolume_unitBall,he,Spherical.mean_abs_inner] at hh
  exact hh

end PettyProjection
end

end OAI
