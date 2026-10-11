import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.Support

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Metric Filter Topology MvPolynomial
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

def restrictContinuous {n : ℕ} (f : Space n → ℝ) (hf : Continuous f) : C(Sphere n, ℝ) :=
  ⟨fun u => f u, hf.comp continuous_subtype_val⟩

lemma polynomialFunction_odd {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous d) (hd : Odd d) : Function.Odd (polynomialFunction p) := by
  intro x
  simpa only [neg_one_smul, hd.neg_one_pow, neg_one_mul] using
    polynomialFunction_smul_argument hp (-1) x

lemma mean_even_mul_odd {n d : ℕ} {p : MvPolynomial (Fin n) ℝ}
    {f : Space n → ℝ} (heven : Function.Even f) (hp : p.IsHomogeneous d) (hd : Odd d) :
    mean (fun u : Sphere n => f u * polynomialFunction p u) = 0 := by
  have h := mean_rotation (LinearIsometryEquiv.neg ℝ : Space n ≃ₗᵢ[ℝ] Space n)
    (fun u : Sphere n => f u * polynomialFunction p u)
  have hh : (fun u : Sphere n =>
      f (sphereMap (LinearIsometryEquiv.neg ℝ) u) *
        polynomialFunction p (sphereMap (LinearIsometryEquiv.neg ℝ) u)) =
      (fun u : Sphere n => -(f u * polynomialFunction p u)) := by
    funext u
    change f (-↑u) * polynomialFunction p (-↑u) = _
    rw [heven, polynomialFunction_odd hp hd, mul_neg]
  rw [hh, mean, integral_neg] at h
  unfold mean at h ⊢
  linarith

lemma projection_odd_zero {n d : ℕ} [NeZero n] {f : Space n → ℝ}
    (hf : Continuous f) (heven : Function.Even f) (hd : Odd d) :
    (harmonicSpace n d).starProjection (toH n (restrictContinuous f hf)) = 0 := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _)
  rintro v ⟨p, hp, rfl⟩
  rw [sub_zero]
  change ⟪toH n (restrictContinuous f hf), toH n (polynomialRestriction n p)⟫ = 0
  rw [inner_toH]
  exact mean_even_mul_odd heven hp.1 hd

/-- A chosen true polynomial representative of a harmonic L² vector. -/
def harmonicRepresentative {n d : ℕ} [NeZero n] (v : harmonicSpace n d) : MvPolynomial (Fin n) ℝ :=
  Classical.choose v.property

/-- The mean-subtracted variance in the probability normalization. -/
def variance {n : ℕ} (f : Sphere n → ℝ) : ℝ := mean (fun u => f u ^ 2) - (mean f) ^ 2

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma line_convex {n : ℕ} {f : Space n → ℝ} (hc : ConvexOn ℝ univ f)
    (x y : Space n) : ConvexOn ℝ univ (fun t : ℝ => f (x + t • y)) := by
  constructor
  · exact convex_univ
  · intro a _ b _ s t hs ht hst
    have h := hc.2 (mem_univ (x + a • y)) (mem_univ (x + b • y)) hs ht hst
    have he : x + (s * a + t * b) • y = s • (x + a • y) + t • (x + b • y) := by
      calc
        _ = (s + t) • x + (s * a + t * b) • y := by rw [hst, one_smul]
        _ = _ := by module
    simpa only [smul_eq_mul, ← he] using h

lemma line_hasDerivAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • y) y t := by
  have h : HasDerivAt (fun s : ℝ => s • y) y t := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const y
  exact h.const_add x

lemma line_second_hasDerivAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x y : E) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (fderiv ℝ (fderiv ℝ f) x y y) 0 := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hh : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    (hfd.differentiable (by norm_num) x).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => x + t • y) y 0 := line_hasDerivAt x y 0
  have hdx : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y))
      (fderiv ℝ (fderiv ℝ f) x y) 0 := by
    have hh' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (x + (0 : ℝ) • y) := by
      simpa only [zero_smul, add_zero] using hh
    exact hh'.comp_hasDerivAt 0 hl
  have hd : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • y) y)
      (fderiv ℝ (fderiv ℝ f) x y y + fderiv ℝ f (x + (0 : ℝ) • y) 0) 0 :=
    hdx.clm_apply (hasDerivAt_const 0 y)
  simpa only [map_zero, add_zero] using hd

lemma hessian_nonneg_of_convex {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x y : Space n) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x y y := by
  have hdf (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • y))
      (fderiv ℝ f (x + t • y) y) t :=
    (hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt x y t)
  have hmono : Monotone (fun t : ℝ => fderiv ℝ f (x + t • y) y) := by
    have h := (line_convex hc x y).monotoneOn_deriv (fun t _ => (hdf t).differentiableAt)
    have heq : deriv (fun t : ℝ => f (x + t • y)) =
        (fun t => fderiv ℝ f (x + t • y) y) := funext fun t => (hdf t).deriv
    rw [heq] at h
    exact monotoneOn_univ.mp h
  rw [← (line_second_hasDerivAt hf x y).deriv]
  exact hmono.deriv_nonneg

lemma rotDeriv_rotDeriv {n : ℕ} (T : Space n →L[ℝ] Space n) {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Space n) :
    rotDeriv T (rotDeriv T f) x =
      fderiv ℝ (fderiv ℝ f) x (T x) (T x) + fderiv ℝ f x (T (T x)) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd := (hfd.differentiable (by norm_num) x).hasFDerivAt.clm_apply T.hasFDerivAt
  change fderiv ℝ (fun y => fderiv ℝ f y (T y)) x (T x) = _
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, add_comm]

lemma generator_square_coord {n : ℕ} (i j a : Fin n) (x : Space n) :
    (generator n i j (generator n i j x)) a =
      2 * (if i = j then if i = a then x a else 0 else 0) -
        (if j = a then x a else 0) - (if i = a then x a else 0) := by
  by_cases hij : i = j <;> by_cases hia : i = a <;> by_cases hja : j = a <;>
    simp_all [generator_apply_coord, eq_comm]; ring

lemma sum_generator_square {n : ℕ} (x : Space n) :
    ∑ i : Fin n, ∑ j : Fin n, generator n i j (generator n i j x) =
      (-2 * ((n : ℝ) - 1)) • x := by
  ext a
  simp only [WithLp.ofLp_sum, Finset.sum_apply, generator_square_coord, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma convex_casimir_lower {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : ConvexOn ℝ univ f) (x : Space n) :
    -((n : ℝ) - 1) * fderiv ℝ f x x ≤ casimir f x := by
  have h (i j : Fin n) : fderiv ℝ f x (generator n i j (generator n i j x)) ≤
      rotDeriv (generator n i j) (rotDeriv (generator n i j) f) x := by
    rw [rotDeriv_rotDeriv _ hf]
    linarith [hessian_nonneg_of_convex hf hc x (generator n i j x)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h i j))
  have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [← map_sum, sum_generator_square, map_smul, smul_eq_mul] at hh
  unfold casimir
  nlinarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Pointwise Convolution
namespace PettyProjection.Spherical

lemma seminorm_continuous (n : ℕ) (g : Seminorm ℝ (Space n)) : Continuous g :=
  continuousOn_univ.mp (g.convexOn.continuousOn isOpen_univ)

lemma seminorm_lipschitz (n : ℕ) (g : Seminorm ℝ (Space n)) :
    ∃ C : ℝ≥0, LipschitzWith C g := by
  obtain ⟨C, hC, hbound⟩ := g.bound_of_continuous_normedSpace (seminorm_continuous n g)
  refine ⟨⟨C, hC.le⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change |g x - g y| ≤ C * dist x y
  exact (abs_sub_map_le_sub g x y).trans (by simpa only [dist_eq_norm] using hbound (x - y))

def normSmooth {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    Space n → ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g : Space n → ℝ)

lemma normSmooth_contDiff {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ 2 (normSmooth g φ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed (seminorm_continuous n g).locallyIntegrable

lemma normSmooth_integrable {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    (x : Space n) : Integrable (fun y => φ.normed volume y * g (x - y)) volume :=
  φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed.locallyIntegrable (seminorm_continuous n g) x

lemma normSmooth_convex {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ univ (normSmooth g φ) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have hi₁ := (normSmooth_integrable g φ x).const_mul a
    have hi₂ := (normSmooth_integrable g φ y).const_mul b
    change (∫ z, φ.normed volume z * g (a • x + b • y - z)) ≤
        a * (∫ z, φ.normed volume z * g (x - z)) + b * (∫ z, φ.normed volume z * g (y - z))
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi₁ hi₂]
    apply integral_mono (normSmooth_integrable g φ (a • x + b • y)) (hi₁.add hi₂)
    intro z
    have he : a • x + b • y - z = a • (x - z) + b • (y - z) := by
      calc
        _ = a • x + b • y - (a + b) • z := by rw [hab, one_smul]
        _ = _ := by module
    have h := mul_le_mul_of_nonneg_left
      (g.convexOn.2 (mem_univ (x-z)) (mem_univ (y-z)) ha hb hab) (φ.nonneg_normed (μ := volume) z)
    simp only [Pi.add_apply]
    rw [he]
    simpa only [smul_eq_mul, mul_add, mul_left_comm] using h

lemma normSmooth_dist_le {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    {C : ℝ≥0} (hC : LipschitzWith C g) (x : Space n) :
    dist (normSmooth g φ x) (g x) ≤ C * φ.rOut := by
  apply φ.dist_normed_convolution_le (seminorm_continuous n g).aestronglyMeasurable
  intro y hy
  exact (hC.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le C.coe_nonneg)

lemma convex_radial_bounds {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f) (x : Space n) :
    f x - f 0 ≤ fderiv ℝ f x x ∧ fderiv ℝ f x x ≤ f ((2 : ℝ) • x) - f x := by
  have hd : HasDerivAt (fun t : ℝ => f (x + t • x)) (fderiv ℝ f x x) 0 := by
    have h : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • x) := by
      simpa only [zero_smul, add_zero] using (hf x).hasFDerivAt
    exact h.comp_hasDerivAt 0 (line_hasDerivAt x x 0)
  have hl := (line_convex hc x x).slope_le_of_hasDerivAt (mem_univ (-1 : ℝ)) (mem_univ 0)
    (by norm_num : (-1 : ℝ) < 0) hd
  have hr := (line_convex hc x x).le_slope_of_hasDerivAt (mem_univ 0) (mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hd
  simpa only [slope, vsub_eq_sub, neg_smul, one_smul, add_neg_cancel,
    zero_smul, add_zero, two_smul, zero_sub, neg_neg, sub_zero, inv_one, smul_eq_mul, one_mul] using And.intro hl hr

lemma normSmooth_radial_dist_le {n : ℕ} (g : Seminorm ℝ (Space n)) (φ : ContDiffBump (0 : Space n))
    {C : ℝ≥0} (hC : LipschitzWith C g) (x : Space n) :
    dist (fderiv ℝ (normSmooth g φ) x x) (g x) ≤ 2 * C * φ.rOut := by
  have h := convex_radial_bounds ((normSmooth_contDiff g φ).differentiable (by norm_num))
    (normSmooth_convex g φ) x
  have hx := normSmooth_dist_le g φ hC x
  have h0 := normSmooth_dist_le g φ hC 0
  have h2 := normSmooth_dist_le g φ hC ((2 : ℝ) • x)
  rw [Real.dist_eq, abs_le] at hx h0 h2 ⊢
  simp only [map_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h0 h2
  constructor <;> linarith

end PettyProjection.Spherical
end

noncomputable section
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Pointwise
namespace PettyProjection.Spherical

lemma sphere_ae_of_radial {n : ℕ} {P : Space n → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (Space n)), P x)
    (hr : ∀ (u : Sphere n) (r : ℝ), 0 < r → P (r • (u : Space n)) → P u) :
    ∀ᵐ (u : Sphere n) ∂sigma n, P (u : Space n) := by
  let ν := Measure.volumeIoiPow (Module.finrank ℝ (Space n) - 1)
  have hν : ν ≠ 0 := by
    intro h
    have he := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ (Space n) - 1)
      (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))
    change ν _ = _ at he
    rw [h] at he
    have hp : 0 < (1 : ℝ) ^ (Module.finrank ℝ (Space n) - 1 + 1) /
        ((Module.finrank ℝ (Space n) - 1 : ℕ) + 1) := by positivity
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) he.symm
  let : NeZero ν := ⟨hν⟩
  have hs : ∀ᵐ (x : ({0}ᶜ : Set (Space n))) ∂(volume : Measure (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n), P (x : Space n) :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space n)).compl).mp
      (ae_restrict_of_ae hP)
  have hm := (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hi := hm.symm (homeomorphUnitSphereProd (Space n)).toMeasurableEquiv
  have hh := hi.quasiMeasurePreserving.ae hs
  have hh' : ∀ᵐ z ∂(surface n).prod ν, P (z.2.1 • (z.1 : Space n)) := by
    change ∀ᵐ z ∂(surface n).prod ν, P (((homeomorphUnitSphereProd (Space n)).symm z : ({0}ᶜ : Set (Space n))) : Space n) at hh
    simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh
  apply Measure.ae_smul_measure (μ := surface n) _ ((surface n univ)⁻¹)
  filter_upwards [Measure.ae_ae_of_ae_prod hh'] with u hu
  obtain ⟨r, hr'⟩ := hu.exists
  exact hr u r r.property hr'

lemma seminorm_ae_differentiable_sphere {n : ℕ} (g : Seminorm ℝ (Space n)) :
    ∀ᵐ (u : Sphere n) ∂sigma n, DifferentiableAt ℝ (g : Space n → ℝ) (u : Space n) := by
  obtain ⟨C, hC⟩ := seminorm_lipschitz n g
  apply sphere_ae_of_radial hC.ae_differentiableAt
  intro u r hr hd
  have hc := (hd.comp (u : Space n) (differentiableAt_id.const_smul r)).const_smul r⁻¹
  have he : (r⁻¹ • ((g : Space n → ℝ) ∘ (r • id))) = (g : Space n → ℝ) := by
    ext x
    simp only [Pi.smul_apply, Function.comp_apply, id_eq, map_smul_eq_mul,
      Real.norm_eq_abs, abs_of_pos hr, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  change DifferentiableAt ℝ (r⁻¹ • ((g : Space n → ℝ) ∘ (r • id))) (u : Space n) at hc
  rw [he] at hc
  exact hc

lemma normSmooth_lipschitz {n : ℕ} (g : Seminorm ℝ (Space n))
    (φ : ContDiffBump (0 : Space n)) {C : ℝ≥0} (hC : LipschitzWith C g) :
    LipschitzWith C (normSmooth g φ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖(∫ z, φ.normed volume z * g (x - z)) -
    (∫ z, φ.normed volume z * g (y - z))‖ ≤ _
  rw [← integral_sub (normSmooth_integrable g φ x) (normSmooth_integrable g φ y)]
  calc
    _ ≤ ∫ z, ‖φ.normed volume z * g (x - z) - φ.normed volume z * g (y - z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, φ.normed volume z * (C * dist x y) := by
      apply integral_mono
        ((normSmooth_integrable g φ x).sub (normSmooth_integrable g φ y)).norm
        (φ.integrable_normed.mul_const _)
      intro z
      change ‖φ.normed volume z * g (x-z) - φ.normed volume z * g (y-z)‖ ≤ _
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa [dist_eq_norm] using hC.dist_le_mul (x-z) (y-z)
    _ = C * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

end PettyProjection.Spherical
end

end OAI
