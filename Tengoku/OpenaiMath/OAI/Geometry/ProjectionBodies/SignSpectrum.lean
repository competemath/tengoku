import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.CosineSpectrum

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

def signFactor (n j : ℕ) (a : ℝ) : ℝ :=
  higherFactor n j 1*(1+a*eigenvalue n (2*j))

lemma signFactor_abs_step {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    |signFactor n (j+1) a| ≤ |signFactor n j a| := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hden : 0 < 1+(n : ℝ)+2*j := by linarith
  have he : 0 ≤ eigenvalue n (2*j) := by
    unfold eigenvalue
    push_cast
    apply mul_nonneg (by positivity)
    linarith
  have he' : 0 ≤ eigenvalue n (2*(j+1)) := by
    unfold eigenvalue
    push_cast
    apply mul_nonneg (by positivity)
    linarith
  have hb : (2*(j : ℝ)-1)*(1+a*eigenvalue n (2*(j+1))) ≤
      (1+(n : ℝ)+2*j)*(1+a*eigenvalue n (2*j)) := by
    have hpos : 0 ≤ a*(((n : ℝ)-2)*(2*j)*(2*j+n)+2*n) := by positivity
    simp only [eigenvalue, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    nlinarith
  simp only [signFactor, higherFactor_succ, abs_mul]
  rw [abs_div, abs_of_pos hden, abs_of_nonpos (by linarith : 1-2*(j : ℝ) ≤ 0), neg_sub,
    abs_of_nonneg (by positivity : 0 ≤ 1+a*eigenvalue n (2*(j+1))),
    abs_of_nonneg (by positivity : 0 ≤ 1+a*eigenvalue n (2*j))]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  simpa only [mul_comm] using hb

lemma signFactor_abs_le_four {n j : ℕ} (hn : 2 ≤ n) (hj : 2 ≤ j) {a : ℝ} (ha : 0 ≤ a) :
    |signFactor n j a| ≤ (1+a*(4*(n+2)))/((n+1)*(n+3)) := by
  have hstep : |signFactor n j a| ≤ |signFactor n 2 a| := by
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (signFactor_abs_step hn (by omega) ha).trans ih
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : signFactor n 2 a = -(1+a*(4*(n+2)))/((n+1)*(n+3)) := by
    norm_num [signFactor, higherFactor, Finset.prod_range_succ, eigenvalue]
    field_simp
    ring
  rw [he, abs_of_nonpos (by exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity) : -(1+a*(4*(n+2)))/((n+1)*(n+3)) ≤ 0)] at hstep
  simpa only [neg_div, neg_neg] using hstep

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma harmonic_inner_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] {d e : ℕ} (hde : d ≠ e)
    {v w : H n} (hv : v ∈ harmonicSpace n d) (hw : w ∈ harmonicSpace n e) :
    ⟪v,w⟫ = 0 := by
  exact harmonicSpace_orthogonal hn hde ⟨v,hv⟩ ⟨w,hw⟩

lemma harmonic_projection_of_mem_ne {n : ℕ} (hn : 2 ≤ n) [NeZero n] {d e : ℕ} (hde : d ≠ e)
    {v : H n} (hv : v ∈ harmonicSpace n e) : (harmonicSpace n d).starProjection v = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  intro w hw
  rw [sub_zero]
  exact harmonic_inner_ne hn hde.symm hv hw

end PettyProjection.Spherical
end

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : ℕ → Submodule ℝ E} [∀ i, CompleteSpace (F i)]

lemma hilbertSum_norm_le_of_projection_bound
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x y : E) {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ i, ‖(F i).starProjection y‖ ≤ c*‖(F i).starProjection x‖) :
    ‖y‖ ≤ c*‖x‖ := by
  have hsq : ‖y‖^2 ≤ c^2*‖x‖^2 := by
    apply hasSum_le _ (hilbertSum_hasSum_projection_norm_sq h y)
      (HasSum.mul_left (c^2) (hilbertSum_hasSum_projection_norm_sq h x))
    intro i
    have h := sq_le_sq₀ (norm_nonneg ((F i).starProjection y))
      (mul_nonneg hc (norm_nonneg ((F i).starProjection x))) |>.mpr (hp i)
    simpa only [mul_pow] using h
  nlinarith [norm_nonneg y, mul_nonneg hc (norm_nonneg x)]

omit [CompleteSpace E] in
lemma inner_projection_both (K : Submodule ℝ E) [CompleteSpace K] (x y : E) :
    ⟪K.starProjection x,K.starProjection y⟫ = ⟪x,K.starProjection y⟫ := by
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem y)]

lemma hilbertSum_hasSum_inner
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ)) (x y : E) :
    HasSum (fun i => ⟪(F i).starProjection x,(F i).starProjection y⟫) ⟪x,y⟫ := by
  simp only [inner_projection_both]
  exact (innerSL ℝ x).hasSum (hilbertSum_hasSum_projection h y)

lemma hilbertSum_multiplier_selfadj
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x y tx ty : E) (c : ℕ → ℝ)
    (hx : ∀ i, (F i).starProjection tx = c i • (F i).starProjection x)
    (hy : ∀ i, (F i).starProjection ty = c i • (F i).starProjection y) :
    ⟪x,ty⟫ = ⟪tx,y⟫ := by
  have h₁ := hilbertSum_hasSum_inner h x ty
  have h₂ := hilbertSum_hasSum_inner h tx y
  simp only [hx, hy, real_inner_smul_left, real_inner_smul_right] at h₁ h₂
  exact h₁.unique h₂

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma casimir_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (casimir f) := by
  unfold casimir
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => continuous_rotDeriv _ (contDiff_rotDeriv _ hf))

def casimirMap {n : ℕ} (f : Space n → ℝ) (hf : ContDiff ℝ 2 f) : C(Sphere n, ℝ) :=
  restrictContinuous (casimir f) (casimir_continuous hf)

lemma casimir_projection {n d : ℕ} [NeZero n] {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (harmonicSpace n d).starProjection (toH n (casimirMap f hf)) =
      -eigenvalue n d • (harmonicSpace n d).starProjection (toH n (restrictContinuous f hf.continuous)) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((harmonicSpace n d).smul_mem _ ((harmonicSpace n d).starProjection_apply_mem _))
  rintro v ⟨p,hp,rfl⟩
  rw [inner_sub_left, real_inner_smul_left, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (show polynomialL2 n p ∈ harmonicSpace n d from ⟨p,hp,rfl⟩)]
  change ⟪toH n (casimirMap f hf),toH n (polynomialRestriction n p)⟫ -
    (-eigenvalue n d)*⟪toH n (restrictContinuous f hf.continuous),toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH, inner_toH]
  change mean (fun x : Sphere n => casimir f x*polynomialFunction p x) -
    (-eigenvalue n d)*mean (fun x : Sphere n => f x*polynomialFunction p x) = 0
  simp_rw [mul_comm (casimir f _)]
  rw [mean_casimir_comm ((polynomialFunction_contDiff p).of_le le_top) hf]
  simp_rw [casimir_harmonic hp.1 hp.2, mul_left_comm (f _) (-eigenvalue n d)]
  rw [mean, integral_const_mul]
  exact sub_self _

def signOperator {n : ℕ} [NeZero n] (a : ℝ) (f : Space n → ℝ) (hf : ContDiff ℝ 2 f) :
    C(Sphere n, ℝ) := cosineMap (restrictContinuous f hf.continuous - a • casimirMap f hf)

lemma signOperator_projection_even {n j : ℕ} (hn : 2 ≤ n) [NeZero n]
    (a : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    (harmonicSpace n (2*j)).starProjection (toH n (signOperator a f hf)) =
      signFactor n j a • (harmonicSpace n (2*j)).starProjection (toH n (restrictContinuous f hf.continuous)) := by
  rw [signOperator, cosine_projection_even hn, map_sub, map_smul, map_sub, map_smul,
    casimir_projection hf, smul_smul, smul_sub, smul_smul, ← sub_smul]
  congr 1
  unfold signFactor
  ring

lemma signOperator_projection_odd {n d : ℕ} [NeZero n]
    (a : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (signOperator a f hf)) = 0 :=
  cosine_projection_odd _ hd

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma cosine_sub_smul {n : ℕ} [NeZero n] {f g : Sphere n → ℝ}
    (hf : Continuous f) (hg : Continuous g) (a : ℝ) (u : Sphere n) :
    cosine (fun x => f x-a*g x) u = cosine f u-a*cosine g u := by
  unfold cosine mean
  simp_rw [mul_sub, mul_left_comm _ a]
  rw [integral_sub (continuous_integrable (by fun_prop)) (continuous_integrable (by fun_prop)),
    integral_const_mul]
  ring

lemma signOperator_apply {n : ℕ} [NeZero n] (a : ℝ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (u : Sphere n) :
    signOperator a f hf u = cosine (fun x : Sphere n => f x) u -
      a*cosine (fun x : Sphere n => casimir f x) u := by
  exact cosine_sub_smul (hf.continuous.comp continuous_subtype_val)
    ((casimir_continuous hf).comp continuous_subtype_val) a u

lemma casimir_const {n : ℕ} (c : ℝ) : casimir (fun _ : Space n => c) = 0 := by
  have hr (X : Space n →L[ℝ] Space n) : rotDeriv X (fun _ => c) = 0 := by
    ext x
    simp [rotDeriv]
  ext x
  simp [casimir, hr, rotDeriv]

lemma mean_casimir_zero {n : ℕ} [NeZero n] {f : Space n → ℝ} (hf : ContDiff ℝ 2 f) :
    mean (fun x : Sphere n => casimir f x) = 0 := by
  have h := mean_casimir_comm (f := fun _ => 1) contDiff_const hf
  simpa only [one_mul, casimir_const, Pi.zero_apply, mul_zero, mean, integral_zero] using h

lemma mean_signOperator {n : ℕ} [NeZero n] (a : ℝ) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) : mean (signOperator a f hf) = mean (fun x : Sphere n => f x) := by
  rw [signOperator, show (cosineMap (restrictContinuous f hf.continuous - a • casimirMap f hf) : Sphere n → ℝ) =
      cosine (restrictContinuous f hf.continuous - a • casimirMap f hf) from rfl,
    mean_cosine (ContinuousMap.continuous _)]
  change mean (fun x : Sphere n => f x-a*casimir f x) = _
  unfold mean
  rw [integral_sub (f := fun x : Sphere n => f x) (g := fun x : Sphere n => a*casimir f x)
    (continuous_integrable (hf.continuous.comp continuous_subtype_val))
    (continuous_integrable (continuous_const.mul ((casimir_continuous hf).comp continuous_subtype_val))),
    integral_const_mul]
  change mean (fun x : Sphere n => f x) - a*mean (fun x : Sphere n => casimir f x) = _
  rw [mean_casimir_zero hf, mul_zero, sub_zero]
  rfl

lemma mean_signOperator_expand {n : ℕ} [NeZero n] (a : ℝ) {f g : Space n → ℝ}
    (hf : Continuous f) (hg : ContDiff ℝ 2 g) :
    mean (fun x : Sphere n => f x*signOperator a g hg x) =
      mean (fun x : Sphere n => f x*cosine (fun y : Sphere n => g y) x) -
        a*mean (fun x : Sphere n => f x*cosine (fun y : Sphere n => casimir g y) x) := by
  simp_rw [signOperator_apply, mul_sub, mul_left_comm (f _) a]
  exact (integral_sub
    (continuous_integrable ((hf.comp continuous_subtype_val).mul (cosine_continuous (hg.continuous.comp continuous_subtype_val))))
    (continuous_integrable (continuous_const.mul ((hf.comp continuous_subtype_val).mul
      (cosine_continuous ((casimir_continuous hg).comp continuous_subtype_val)))))).trans
    (by
      change _ - (∫ x : Sphere n, a * (f x * cosine (fun y : Sphere n => casimir g y) x) ∂sigma n) = _
      rw [integral_const_mul]
      rfl)

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace
namespace PettyProjection.Spherical

lemma inner_Q_Q {n : ℕ} [NeZero n] (x y : H n) :
    ⟪Q n x,Q n y⟫ = ⟪Q n x,y⟫ := by
  change ⟪(lowSpace n)ᗮ.starProjection x,(lowSpace n)ᗮ.starProjection y⟫ = _
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr ((lowSpace n)ᗮ.starProjection_apply_mem y)]
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

def radialField {n : ℕ} (f : Space n → ℝ) (u : Sphere n) : Space n := f u • (u : Space n)
def tangentField {n : ℕ} (f : Space n → ℝ) (u : Sphere n) : Space n := sphereGradient f u

def signField {n : ℕ} (k : ℝ) (f : Space n → ℝ) (u : Sphere n) : Space n :=
  radialField f u + k⁻¹ • tangentField f u

lemma radialField_continuous {n : ℕ} {f : Space n → ℝ} (hf : Continuous f) :
    Continuous (radialField f) := (hf.comp continuous_subtype_val).smul continuous_subtype_val

lemma tangentField_continuous {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (tangentField f) := (sphereGradient_continuous hf).comp continuous_subtype_val

lemma signedPair_radial_radial {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    signedPair (radialField f) (radialField g) = cosineConstant n *
      mean (fun u : Sphere n => f u*cosine (fun v : Sphere n => g v) u) := by
  rw [signedPair_eq (radialField_continuous hf) (radialField_continuous hg)]
  have hi (u v : Sphere n) :
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪radialField f u,radialField g v⟫ =
        f u*(|⟪(u : Space n),(v : Space n)⟫| * g v) := by
    simp only [radialField, real_inner_smul_left, real_inner_smul_right]
    calc
      _ = (Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪(u : Space n),(v : Space n)⟫)*f u*g v := by ring
      _ = _ := by rw [sign_mul_self]; ring
  simp_rw [hi, mean, integral_const_mul]
  simp only [cosine, mean, ← mul_div_assoc, integral_div]
  field_simp [(cosineConstant_pos n).ne']

lemma signedPair_tangent_radial {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : Continuous g) :
    signedPair (tangentField f) (radialField g) = -cosineConstant n *
      mean (fun u : Sphere n => g u*cosine (fun v : Sphere n => casimir f v) u) := by
  rw [signedPair_eq_swap (tangentField_continuous (hf.of_le (by norm_num))) (radialField_continuous hg)]
  have hi (u v : Sphere n) :
      Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪tangentField f u,radialField g v⟫ =
        g v*(Real.sign ⟪(v : Space n),(u : Space n)⟫*⟪sphereGradient f u,(v : Space n)⟫) := by
    simp only [radialField, tangentField, real_inner_smul_right]
    rw [real_inner_comm (u : Space n) (v : Space n)]
    ring
  simp_rw [hi, mean, integral_const_mul]
  change mean (fun v : Sphere n => g v * mean (fun u : Sphere n =>
    Real.sign ⟪(v : Space n),(u : Space n)⟫ * ⟪sphereGradient f u,(v : Space n)⟫)) = _
  simp_rw [mean_sign_gradient_radial hf]
  simp only [cosine, mean, ← mul_div_assoc, integral_div, mul_neg]
  rw [integral_neg]
  have hb := (cosineConstant_pos n).ne'
  field_simp

lemma signedPair_tangent_tangent {n : ℕ} [NeZero n] {f g : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    signedPair (tangentField f) (tangentField g) = ((n : ℝ)-1)*
      signedPair (radialField f) (tangentField g) := by
  rw [signedPair_eq_swap (tangentField_continuous hf) (tangentField_continuous hg),
    signedPair_eq_swap (radialField_continuous hf.continuous) (tangentField_continuous hg)]
  have hi (v : Sphere n) :
      mean (fun u : Sphere n => Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪tangentField f u,tangentField g v⟫) =
        ((n : ℝ)-1)*mean (fun u : Sphere n => Real.sign ⟪(u : Space n),(v : Space n)⟫ * ⟪radialField f u,tangentField g v⟫) := by
    have h := mean_sign_gradient_tangent hf (v : Space n) (sphereGradient g v)
      (by rw [real_inner_comm]; exact sphereGradient_tangent g v)
    convert h using 1
    · congr 1
      funext u
      rw [real_inner_comm (u : Space n) (v : Space n)]
      rfl
    · congr 1
      congr 1
      funext u
      simp only [radialField, tangentField, real_inner_smul_left]
      rw [real_inner_comm (u : Space n) (v : Space n)]
      ring
  simp_rw [hi]
  exact integral_const_mul _ _

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped ENNReal RealInnerProductSpace Gradient
namespace PettyProjection.Spherical

lemma signField_continuous {n : ℕ} (k : ℝ) {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (signField k f) :=
  (radialField_continuous hf.continuous).add ((tangentField_continuous hf).const_smul k⁻¹)

end PettyProjection.Spherical
end

end OAI
