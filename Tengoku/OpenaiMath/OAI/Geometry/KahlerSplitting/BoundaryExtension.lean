import Tengoku.OpenaiMath.OAI.Geometry.KahlerSplitting.SmallAnnuli

namespace OAI

noncomputable section
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open Set Metric Filter Topology Asymptotics
open scoped Interval
open Set Filter Topology Metric
open Set Filter Topology Metric Complex
open scoped Real
open Set Filter Topology
open scoped Manifold ContDiff
open Set MeasureTheory
open scoped ContDiff
open scoped Manifold ContDiff ENNReal
open scoped Manifold ENNReal NNReal
open Set Metric Filter Topology
open scoped Manifold
open Set Metric
open Set MeasureTheory Filter Topology
open scoped ENNReal
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
open Set

namespace UniversalCoverSplitting

lemma exists_boundary_scales {x₀ k η : ℝ} (hx : x₀ < 0) (hk : 0 < k) (hη : 0 < η)
    (N : ℕ) : ∃ t : ℝ, 0 < t ∧ -t^4 ∈ Ico x₀ 0 ∧
      ∀ i ≤ N, t^4 < η*((5:ℝ)^i*t^3) ∧ 2*((5:ℝ)^i*t^3) < k*t^2 := by
  have h5 : 0 < (5:ℝ)^N := pow_pos (by norm_num) _
  have hneg : 0 < -x₀ := neg_pos.mpr hx
  have hmin : 0 < min 1 (min (-x₀) (min η (k/(2*(5:ℝ)^N)))) := by positivity
  obtain ⟨t,ht,htm⟩ := exists_between hmin
  have ht1 : t < 1 := htm.trans_le (min_le_left _ _)
  have htX : t < -x₀ := htm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htη : t < η := htm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htk : t < k/(2*(5:ℝ)^N) := htm.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ht4 : t^4 ≤ t := by
    calc
      t^4 = t*t^3 := by ring
      _ ≤ t*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht.le ht1.le) ht.le
      _ = t := mul_one _
  refine ⟨t,ht,⟨by linarith,neg_neg_of_pos (pow_pos ht _)⟩,?_⟩
  intro i hi
  have hp : 1 ≤ (5:ℝ)^i := one_le_pow₀ (by norm_num)
  have hpN : (5:ℝ)^i ≤ 5^N := pow_le_pow_right₀ (by norm_num) hi
  have ht3 : 0 < t^3 := pow_pos ht _
  have ht2 : 0 < t^2 := pow_pos ht _
  constructor
  · calc
      t^4 = t*(t^3) := by ring
      _ < η*t^3 := mul_lt_mul_of_pos_right htη ht3
      _ ≤ η*((5:ℝ)^i*t^3) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left ht3.le hp) hη.le
  · have htk' : 2*(5:ℝ)^N*t < k := by
      have h := (lt_div_iff₀ (mul_pos (by norm_num) h5)).mp htk
      nlinarith
    calc
      2*((5:ℝ)^i*t^3) ≤ 2*((5:ℝ)^N*t^3) := by gcongr
      _ = (2*(5:ℝ)^N*t)*t^2 := by ring
      _ < k*t^2 := mul_lt_mul_of_pos_right htk' ht2

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsMixedBox.eqOn_of_slice_in_domain (h₁ : Integrable S.projection)
    (h₂ : Integrable (complementaryProjection S)) {c : ℂ × ℂ} {hc : c.1 ≠ c.2}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {D : Set ℂ} (hD : IsOpen D) {v w : ℂ} (hv : v ∈ D)
    {f g : ℂ × ℂ → X.Carrier} (hf : IsMixedBox (S := S) c hc U f)
    (hg : IsMixedBox (S := S) c hc U g)
    (hmap : ∀ z ∈ D, (w,z) ∈ U) (he : ∀ z ∈ D, f (w,z) = g (w,z)) : EqOn f g U := by
  let M := mixedEquiv c hc
  let p : ℂ × ℂ := (c.1*w,c.2*w)
  have hcalc (z : ℂ) : separatedAffine p (1,1) (z,z) = M (w,z) := by
    ext <;> simp [p,M,separatedAffine,mixedEquiv_apply,add_comm]
  have hmo : IsOpen (M '' U) := M.toHomeomorph.isOpenMap _ hU
  have hh : (f ∘ M.symm) =ᶠ[𝓝 (M (w,v))] (g ∘ M.symm) := by
    rw [← hcalc]
    apply box_shifted_diagonal_germ_unique h₁ h₂ hmo hD hf hg p hv
    · intro z hz
      rw [hcalc]
      exact mem_image_of_mem M (hmap z hz)
    · intro z hz
      change f (M.symm (separatedAffine p (1,1) (z,z))) = g (M.symm (separatedAffine p (1,1) (z,z)))
      rw [hcalc,M.symm_apply_apply]
      exact he z hz
  have hevent : f =ᶠ[𝓝 (w,v)] g := by
    simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh.comp_tendsto M.continuous.continuousAt
  exact holomorphic_manifold_eqOn_of_preconnected_of_eventuallyEq hU hUc
    hf.holomorphic hg.holomorphic (hmap v hv) hevent

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

def separatedHomeomorph (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) where
  toFun := separatedAffine p b
  invFun := separatedAffine (-p.1/b.1,-p.2/b.2) (b.1⁻¹,b.2⁻¹)
  left_inv z := by
    ext <;> dsimp [separatedAffine] <;> field_simp <;> ring
  right_inv z := by
    ext <;> dsimp [separatedAffine] <;> field_simp <;> ring
  continuous_toFun := by unfold separatedAffine; fun_prop
  continuous_invFun := by unfold separatedAffine; fun_prop

@[simp] lemma separatedHomeomorph_apply (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (z : ℂ × ℂ) :
    separatedHomeomorph p b hb₁ hb₂ z = separatedAffine p b z := rfl

@[simp] lemma separatedHomeomorph_symm_apply (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (z : ℂ × ℂ) :
    (separatedHomeomorph p b hb₁ hb₂).symm z =
      separatedAffine (-p.1/b.1,-p.2/b.2) (b.1⁻¹,b.2⁻¹) z := rfl

lemma separatedAffine_convex_preimage {U : Set (ℂ × ℂ)} (hU : Convex ℝ U) (p b : ℂ × ℂ) :
    Convex ℝ (separatedAffine p b ⁻¹' U) :=
  (hU.translate_preimage_right p).linear_preimage ((separatedLinear b).restrictScalars ℝ).toLinearMap

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

lemma IsBox.comp_separatedHomeomorph_symm {U V : Set (ℂ × ℂ)} (hU : IsOpen U)
    {f : ℂ × ℂ → X.Carrier} (hf : IsBox S U f)
    (p b : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0)
    (hmap : MapsTo (separatedHomeomorph p b hb₁ hb₂).symm V U) :
    IsBox S V (f ∘ (separatedHomeomorph p b hb₁ hb₂).symm) :=
  hf.comp_separatedAffine hU (-p.1/b.1,-p.2/b.2) (b.1⁻¹,b.2⁻¹) hmap

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma contDiffAt_quadratic_remainder {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ z ∈ ball (0:E) r,
      |f z-f 0-fderiv ℝ f 0 z| ≤ M*‖z‖^2 := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K,T,hT,hLip⟩ := hdf.exists_lipschitzOnWith
  have hdiff : ∀ᶠ z in 𝓝 (0:E), DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono (fun z h ↦ h.differentiableAt (by norm_num))
  obtain ⟨r,hr,hrT⟩ := Metric.mem_nhds_iff.mp (inter_mem hT hdiff)
  have h0T : (0:E) ∈ T := (hrT (mem_ball_self hr)).1
  let D := fderiv ℝ f 0
  let R : E → ℝ := fun z ↦ f z-f 0-D z
  have hD (z : E) (hz : z ∈ ball (0:E) r) : HasFDerivAt R (fderiv ℝ f z-D) z :=
    ((hrT hz).2.hasFDerivAt.sub_const (f 0)).sub D.hasFDerivAt
  refine ⟨r,(K:ℝ)+1,hr,by positivity,?_⟩
  intro z hz
  have hsub : closedBall (0:E) ‖z‖ ⊆ ball 0 r := closedBall_subset_ball (by simpa using hz)
  have hb (u : E) (hu : u ∈ closedBall (0:E) ‖z‖) : ‖fderiv ℝ f u-D‖ ≤ (K:ℝ)*‖z‖ := by
    have h := hLip.dist_le_mul u ((hrT (hsub hu)).1) 0 h0T
    rw [dist_eq_norm,dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa using hu) K.coe_nonneg)
  have h := (convex_closedBall (0:E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u hu ↦ (hD u (hsub hu)).hasFDerivWithinAt) hb
    (mem_closedBall_self (norm_nonneg z)) (by simp : z ∈ closedBall (0:E) ‖z‖)
  have h' : |f z-f 0-D z| ≤ (K:ℝ)*‖z‖*‖z‖ := by
    simpa only [R,map_zero,sub_self,sub_zero,Real.norm_eq_abs] using h
  dsimp [D] at h'
  nlinarith [sq_nonneg ‖z‖]

end UniversalCoverSplitting

open Set Metric Filter Topology
namespace UniversalCoverSplitting

lemma exists_parabolic_interior_disks {ρ : ℂ × ℂ → ℝ} {U : Set (ℂ × ℂ)}
    (hρ : ContDiffAt ℝ 2 ρ 0) (hρ0 : ρ 0 = 0) {c e : ℝ} (hc : 0 < c) (he : 0 < e)
    (hD : ∀ (x : ℝ) (v : ℂ), fderiv ℝ ρ 0 ((x:ℂ),v) = c*x)
    (hU : ∀ z ∈ ball (0:ℂ × ℂ) e, ρ z < 0 → z ∈ U) :
    ∃ a k : ℝ, a < 0 ∧ 0 < k ∧ ∀ x ∈ Ico a 0,
      MapsTo (fun z : ℂ ↦ ((x:ℂ),z)) (closedBall 0 (k*Real.sqrt (-x))) U := by
  obtain ⟨r,M,hr,hM,hrem⟩ := contDiffAt_quadratic_remainder hρ
  let R := min r e
  have hR : 0 < R := lt_min hr he
  let k := Real.sqrt (c/(4*M))
  have hk : 0 < k := Real.sqrt_pos.mpr (by positivity)
  have hk2 : k^2 = c/(4*M) := Real.sq_sqrt (by positivity)
  have hkM : M*k^2 = c/4 := by rw [hk2]; field_simp
  have hm : 0 < min R (min (c/(4*M)) (R^2/(k^2+1))) := by positivity
  obtain ⟨d,hd,hdm⟩ := exists_between hm
  have hdR : d < R := hdm.trans_le (min_le_left _ _)
  have hdM : d < c/(4*M) := hdm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdk : d < R^2/(k^2+1) := hdm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨-d,k,neg_neg_of_pos hd,hk,?_⟩
  intro x hx v hv
  have hs : 0 < -x := neg_pos.mpr hx.2
  have hsd : -x ≤ d := by linarith [hx.1]
  have hvn : ‖v‖ ≤ k*Real.sqrt (-x) := by simpa using hv
  have hvsq : ‖v‖^2 ≤ k^2*(-x) := by
    have h := sq_le_sq₀ (norm_nonneg v) (mul_nonneg hk.le (Real.sqrt_nonneg _)) |>.mpr hvn
    rw [mul_pow,Real.sq_sqrt hs.le] at h
    exact h
  have hvr : ‖v‖ < R := by
    have hdk' := (lt_div_iff₀ (by positivity : 0 < k^2+1)).mp hdk
    have hks := mul_le_mul_of_nonneg_left hsd (sq_nonneg k)
    nlinarith [norm_nonneg v]
  have hzR : ((x:ℂ),v) ∈ ball (0:ℂ × ℂ) R := by
    rw [mem_ball_zero_iff,Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hx.2]
    exact max_lt (hsd.trans_lt hdR) hvr
  have hzNorm : ‖((x:ℂ),v)‖^2 ≤ x^2+‖v‖^2 := by
    rw [Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hx.2]
    rcases le_total (-x) ‖v‖ with h|h
    · rw [max_eq_right h]; nlinarith [sq_nonneg x]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖v‖]
  have hsM : M*(-x) ≤ c/4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4*M)).mp (hsd.trans hdM.le)
    nlinarith
  have hquad : M*‖((x:ℂ),v)‖^2 ≤ c*(-x)/2 := by
    have h₁ := mul_le_mul_of_nonneg_left hzNorm hM.le
    have h₂ := mul_le_mul_of_nonneg_left hvsq hM.le
    have h₃ := mul_le_mul_of_nonneg_right hsM hs.le
    have h₄ : M*(k^2*(-x)) = c/4*(-x) := by rw [← mul_assoc,hkM]
    nlinarith
  have hbound := hrem ((x:ℂ),v) ((ball_subset_ball (min_le_left r e)) hzR)
  rw [hρ0,sub_zero,hD] at hbound
  have hupper := (le_abs_self (ρ ((x:ℂ),v)-c*x)).trans hbound
  apply hU _ ((ball_subset_ball (min_le_right r e)) hzR)
  nlinarith [mul_pos hc hs]

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting

def mixedSource (p b c : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (hc : c.1 ≠ c.2) :
    (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  (mixedEquiv c hc).toHomeomorph.trans (separatedHomeomorph p b hb₁ hb₂)

@[simp] lemma mixedSource_zero (p b c : ℂ × ℂ) (hb₁ : b.1 ≠ 0) (hb₂ : b.2 ≠ 0) (hc : c.1 ≠ c.2) :
    mixedSource p b c hb₁ hb₂ hc 0 = p := by
  ext <;> simp [mixedSource,separatedAffine]

variable {n r s : ℕ} {X : ComplexManifold n} {S : HolomorphicSplitting X r s}

end UniversalCoverSplitting

end

end OAI
