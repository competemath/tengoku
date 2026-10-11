import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.Chaining

namespace OAI

/-! Gaussian correlation and symmetric convex events. -/

section

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix Gain
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def blockCov (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (t : ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks A (t • B) (t • B.transpose) D

lemma blockCov_schur {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ) (t : ℝ) :
    (blockCov A B D t).det = A.det * (D - t ^ 2 • (B.transpose * A⁻¹ * B)).det := by
  let _ := hA.isUnit.invertible
  rw [blockCov, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 2
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma blockCov_affine (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (D : Matrix κ κ ℝ)
    (t : ℝ) :
    blockCov A B D t = t • blockCov A B D 1 + (1 - t) • blockCov A B D 0 := by
  ext (i | i) (j | j) <;> simp [blockCov, fromBlocks] <;> ring

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma blockCov_diag_posDef {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ}
    {D : Matrix κ κ ℝ} (h : (blockCov A B D 1).PosDef) : A.PosDef ∧ D.PosDef := by
  constructor
  · exact h.submatrix Sum.inl_injective
  · exact h.submatrix Sum.inr_injective

lemma schur_posDef {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (h : (blockCov A B D 1).PosDef) : (D - B.transpose * A⁻¹ * B).PosDef := by
  have hA := (blockCov_diag_posDef h).1
  let _ := hA.isUnit.invertible
  have he : blockCov A B D 1 = fromBlocks A B Bᴴ D := by
    simp only [blockCov, one_smul, conjTranspose_eq_transpose_of_trivial]
  have hs : (D - B.transpose * A⁻¹ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (hA.fromBlocks₁₁ B D).mp (he ▸ h.posSemidef)
  apply hs.posDef_iff_det_ne_zero.mpr
  intro hz
  have hd := blockCov_schur hA B D 1
  simp only [one_pow, one_smul, hz, mul_zero] at hd
  exact h.det_pos.ne' hd

lemma blockCov_posDef {A : Matrix ι ι ℝ} {B : Matrix ι κ ℝ} {D : Matrix κ κ ℝ}
    (h : (blockCov A B D 1).PosDef) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (blockCov A B D t).PosDef := by
  have hA := (blockCov_diag_posDef h).1
  let _ := hA.isUnit.invertible
  have hK : (B.transpose * A⁻¹ * B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hA.posSemidef.inv.conjTranspose_mul_mul_same B
  have he : D - t ^ 2 • (B.transpose * A⁻¹ * B) =
      (D - B.transpose * A⁻¹ * B) + (1 - t ^ 2) • (B.transpose * A⁻¹ * B) := by
    module
  have hs : (D - t ^ 2 • (B.transpose * A⁻¹ * B)).PosDef := by
    rw [he]
    exact (schur_posDef h).add_posSemidef (hK.smul (by nlinarith [ht.1, ht.2]))
  have he' : blockCov A B D t = fromBlocks A (t • B) (t • B)ᴴ D := by
    simp only [blockCov, conjTranspose_eq_transpose_of_trivial, transpose_smul]
  have hp : (blockCov A B D t).PosSemidef := by
    rw [he', hA.fromBlocks₁₁]
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two] using hs.posSemidef
  apply hp.posDef_iff_det_ne_zero.mpr
  rw [blockCov_schur hA]
  exact mul_ne_zero hA.det_pos.ne' hs.det_pos.ne'

def interpolate (p : ι → Bool) (R : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => if p i = p j then R i j else t * R i j

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interpolate_one (p : ι → Bool) (R : Matrix ι ι ℝ) : interpolate p R 1 = R := by
  ext i j
  simp [interpolate]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interpolate_blocks (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.IsHermitian) (t : ℝ) :
    let e := Equiv.sumCompl (fun i => p i = true)
    (interpolate p R t).submatrix e e =
      blockCov (R.submatrix (Subtype.val : {i // p i = true} → ι) Subtype.val)
        (R.submatrix (Subtype.val : {i // p i = true} → ι)
          (Subtype.val : {i // ¬ p i = true} → ι))
        (R.submatrix (Subtype.val : {i // ¬ p i = true} → ι) Subtype.val) t := by
  dsimp only
  ext (i | i) (j | j) <;> dsimp [interpolate, blockCov, fromBlocks, Equiv.sumCompl]
  · simp only [i.prop, j.prop, ↓reduceIte]
  · simp only [i.prop, Bool.eq_false_iff.mpr j.prop, Bool.true_eq_false, ↓reduceIte]
  · simp only [Bool.eq_false_iff.mpr i.prop, j.prop, Bool.false_eq_true, ↓reduceIte]
    rw [show R (↑i) (↑j) = R (↑j) (↑i) from (hR.apply _ _).symm]
  · simp only [Bool.eq_false_iff.mpr i.prop, Bool.eq_false_iff.mpr j.prop, ↓reduceIte]

omit [Fintype κ] [DecidableEq κ] in
lemma interpolate_posDef (p : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (interpolate p R t).PosDef := by
  let e := Equiv.sumCompl (fun i => p i = true)
  have h : ((interpolate p R 1).submatrix e e).PosDef := by
    rw [interpolate_one]
    exact hR.submatrix e.injective
  rw [interpolate_blocks p hR.1 1] at h
  have ht' := blockCov_posDef h ht
  rw [← interpolate_blocks p hR.1 t] at ht'
  have hp := ht'.submatrix e.symm.injective
  have he : ((interpolate p R t).submatrix e e).submatrix e.symm e.symm =
      interpolate p R t := by ext i j; simp [submatrix]
  exact he ▸ hp

omit [Fintype κ] [DecidableEq κ] in
lemma interpolate_det_differentiable (p : ι → Bool) (R : Matrix ι ι ℝ) :
    Differentiable ℝ (fun t => (interpolate p R t).det) := by
  have he (i j : ι) : Differentiable ℝ (fun t => interpolate p R t i j) := by
    dsimp [interpolate]
    split_ifs <;> fun_prop
  simp only [Matrix.det_apply']
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  exact Differentiable.fun_finsetProd (fun i _ => he _ _)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma interpolate_submatrix {η : Type*} (p : ι → Bool) (R : Matrix ι ι ℝ)
    (f : η → ι) (t : ℝ) :
    (interpolate p R t).submatrix f f = interpolate (p ∘ f) (R.submatrix f f) t := rfl

omit [Fintype κ] [DecidableEq κ] in
lemma det_diagonal_mul_add_one (R : Matrix ι ι ℝ) (z : ι → ℝ) :
    (diagonal z * R + 1).det = ∑ S : Finset ι,
      (∏ i ∈ S, z i) * (R.submatrix (Subtype.val : S → ι) Subtype.val).det := by
  change detRowAlternating ((fun i j => (diagonal z * R) i j) +
    (fun i j => (1 : Matrix ι ι ℝ) i j)) = _
  rw [detRowAlternating.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have he : S.piecewise (diagonal z * R) (1 : Matrix ι ι ℝ) =
      fun i => (if i ∈ S then z i else 1) • S.piecewise R (1 : Matrix ι ι ℝ) i := by
    ext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp_all
  rw [he, detRowAlternating.map_smul_univ]
  simp only [Finset.prod_ite_mem, Finset.univ_inter]
  change _ * (Matrix.of (S.piecewise R.row (1 : Matrix ι ι ℝ).row)).det = _
  rw [det_piecewise_one_eq_submatrix_det]

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

lemma integral_exp_square_gaussian {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (-t * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 + t) / 2) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [smul_eq_mul, he, integral_const_mul, integral_gaussian]
  rw [show Real.pi / ((1 + t) / 2) = (2 * Real.pi) / (1 + t) by rw [div_div_eq_mul_div]; ring]
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma integrable_exp_square_gaussian {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ => Real.exp (-t * x ^ 2 / 2)) (gaussianReal 0 1) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _)) (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open scoped RealInnerProductSpace

lemma eigenvector_toEuclideanCLM {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  exact hA.mulVec_eigenvectorBasis i

lemma quadratic_eigenbasis {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) :
    ⟪∑ i, x i • hA.eigenvectorBasis i,
      toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ =
      ∑ i, hA.eigenvalues i * x i ^ 2 := by
  simp only [map_sum, map_smul, eigenvector_toEuclideanCLM, smul_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hA.eigenvectorBasis.inner_eq_ite]
  simp [mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma det_one_add_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (1 + A).det = ∏ i, (1 + hA.eigenvalues i) := by
  have he : 1 + A = (Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary)
      (diagonal (fun i => 1 + hA.eigenvalues i)) := by
    rw [show diagonal (fun i => 1 + hA.eigenvalues i) =
      1 + diagonal (RCLike.ofReal ∘ hA.eigenvalues) by
      simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq,
        ← diagonal_one, ← diagonal_add]]
    rw [map_add, map_one, ← hA.spectral_theorem]
  rw [he]
  simp only [Matrix.det_map', det_diagonal]

lemma quadratic_laplace_stdGaussian {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = (Real.sqrt (1 + A).det)⁻¹ := by
  have he (x : ι → ℝ) :
      Real.exp (-⟪∑ i, x i • hA.1.eigenvectorBasis i,
        toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.1.eigenvectorBasis i)⟫ / 2) =
      ∏ i, Real.exp (-hA.1.eigenvalues i * x i ^ 2 / 2) := by
    rw [quadratic_eigenbasis, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div, neg_mul, Finset.sum_neg_distrib, neg_div]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.1.eigenvectorBasis,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [he]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => Real.exp (-hA.1.eigenvalues i * x ^ 2 / 2))]
  simp_rw [integral_exp_square_gaussian (hA.eigenvalues_nonneg _)]
  rw [det_one_add_eigenvalues hA.1, Real.sqrt_prod]
  · simp
  · intro i _
    linarith [hA.eigenvalues_nonneg i]

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_diagonal (z : ι → ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) (diagonal z) x⟫ = ∑ i, z i * x i ^ 2 := by
  rw [inner_toEuclideanCLM]
  simp only [dotProduct, mulVec_diagonal, pow_two]
  congr 1
  ext i
  ring

lemma quadratic_sandwich (S D : Matrix ι ι ℝ) (hS : S.IsHermitian)
    (x : EuclideanSpace ℝ ι) :
    ⟪toEuclideanCLM (𝕜 := ℝ) S x,
      toEuclideanCLM (𝕜 := ℝ) D (toEuclideanCLM (𝕜 := ℝ) S x)⟫ =
      ⟪x, toEuclideanCLM (𝕜 := ℝ) (S * D * S) x⟫ := by
  have hs : IsSelfAdjoint (toEuclideanCLM (𝕜 := ℝ) S) := hS.isSelfAdjoint.map _
  rw [← ContinuousLinearMap.adjoint_inner_right, hs.adjoint_eq]
  simp only [map_mul, mul_apply_eq_comp]

lemma sqrt_sandwich_psd {R : Matrix ι ι ℝ} (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (CFC.sqrt R * diagonal z * CFC.sqrt R).PosSemidef := by
  have hD : (diagonal z).PosSemidef := posSemidef_diagonal_iff.mpr hz
  have hS : (CFC.sqrt R).IsHermitian := (CFC.sqrt_nonneg R).isSelfAdjoint
  simpa only [hS.eq] using hD.conjTranspose_mul_mul_same (CFC.sqrt R)

lemma det_one_add_sqrt_sandwich {R : Matrix ι ι ℝ} (hR : R.PosSemidef) (z : ι → ℝ) :
    (1 + CFC.sqrt R * diagonal z * CFC.sqrt R).det = (diagonal z * R + 1).det := by
  rw [Matrix.mul_assoc, det_one_add_mul_comm (CFC.sqrt R) (diagonal z * CFC.sqrt R),
    Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self R hR.nonneg, add_comm]

lemma det_diagonal_mul_add_one_pos {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) : 0 < (diagonal z * R + 1).det := by
  rw [← det_one_add_sqrt_sandwich hR z]
  exact ((show (1 : Matrix ι ι ℝ).PosDef from Matrix.PosDef.one).add_posSemidef (sqrt_sandwich_psd z hz)).det_pos

lemma quadratic_laplace_multivariateGaussian {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-(∑ i, z i * x i ^ 2) / 2)
      ∂multivariateGaussian 0 R) = (Real.sqrt (diagonal z * R + 1).det)⁻¹ := by
  rw [multivariateGaussian,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [zero_add, ← quadratic_diagonal,
    quadratic_sandwich _ _ (CFC.sqrt_nonneg R).isSelfAdjoint]
  rw [quadratic_laplace_stdGaussian (sqrt_sandwich_psd z hz),
    det_one_add_sqrt_sandwich hR z]

lemma integrable_quadratic_exp {R : Matrix ι ι ℝ}
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-(∑ i, z i * x i ^ 2) / 2))
      (multivariateGaussian 0 R) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hsum : 0 ≤ ∑ i, z i * x i ^ 2 := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hz i) (sq_nonneg _))
  linarith

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def laplaceKernel (z x : ι → ℝ) : ℝ := Real.exp (-∑ i, z i * x i)

omit [DecidableEq ι] in
lemma laplaceKernel_nonneg (z x : ι → ℝ) : 0 ≤ laplaceKernel z x :=
  (Real.exp_pos _).le

omit [DecidableEq ι] in
lemma laplaceKernel_le_one {z x : ι → ℝ} (hz : ∀ i, 0 ≤ z i) (hx : ∀ i, 0 ≤ x i) :
    laplaceKernel z x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => mul_nonneg (hz i) (hx i)))

omit [DecidableEq ι] in
lemma laplaceKernel_add (z x y : ι → ℝ) :
    laplaceKernel z (x + y) = laplaceKernel z x * laplaceKernel z y := by
  simp only [laplaceKernel, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    neg_add, Real.exp_add]

omit [DecidableEq ι] in
lemma continuous_laplaceKernel (z : ι → ℝ) : Continuous (laplaceKernel z) := by
  unfold laplaceKernel
  fun_prop

omit [DecidableEq ι] in
lemma measurableSet_nonnegative : MeasurableSet {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))

noncomputable def squareLaw (R : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (multivariateGaussian 0 R).map (fun x : EuclideanSpace ℝ ι => fun i => x i ^ 2 / 2)

lemma squareLaw_nonneg (R : Matrix ι ι ℝ) :
    ∀ᵐ x ∂squareLaw R, ∀ i, 0 ≤ x i := by
  rw [squareLaw, ae_map_iff (by fun_prop) measurableSet_nonnegative]
  filter_upwards [] with x i
  positivity

omit [DecidableEq ι] in
lemma integrable_laplaceKernel {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    Integrable (laplaceKernel z) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (continuous_laplaceKernel _).aestronglyMeasurable
  filter_upwards [hμ] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (laplaceKernel_nonneg _ _)]
  exact laplaceKernel_le_one hz hx

lemma laplace_squareLaw {R : Matrix ι ι ℝ} (hR : R.PosSemidef)
    {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    (∫ x, laplaceKernel z x ∂squareLaw R) =
      (Real.sqrt (diagonal z * R + 1).det)⁻¹ := by
  rw [squareLaw, integral_map (Measurable.aemeasurable (by fun_prop))
    (continuous_laplaceKernel _).aestronglyMeasurable]
  simp only [laplaceKernel, ← mul_div_assoc, ← Finset.sum_div]
  simpa only [neg_div] using quadratic_laplace_multivariateGaussian hR hz

noncomputable def sumLaw (μ ν : Measure (ι → ℝ)) : Measure (ι → ℝ) :=
  (μ.prod ν).map (fun x => x.1 + x.2)

omit [DecidableEq ι] in
lemma sumLaw_nonneg {μ ν : Measure (ι → ℝ)} [SFinite μ] [SFinite ν]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (hν : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i) :
    ∀ᵐ x ∂sumLaw μ ν, ∀ i, 0 ≤ x i := by
  rw [sumLaw, ae_map_iff (by fun_prop) measurableSet_nonnegative]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_nonnegative.preimage (by fun_prop))).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact fun i => add_nonneg (hx i) (hy i)

omit [DecidableEq ι] in
lemma laplace_sumLaw {μ ν : Measure (ι → ℝ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (z : ι → ℝ) :
    (∫ x, laplaceKernel z x ∂sumLaw μ ν) =
      (∫ x, laplaceKernel z x ∂μ) * (∫ x, laplaceKernel z x ∂ν) := by
  rw [sumLaw, integral_map (Measurable.aemeasurable (by fun_prop))
    (continuous_laplaceKernel _).aestronglyMeasurable]
  simp only [laplaceKernel_add]
  exact integral_prod_mul _ _

noncomputable def tripleSquareLaw (R : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  sumLaw (squareLaw R) (sumLaw (squareLaw R) (squareLaw R))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma polynomial_euler_eval (p : ℝ[X]) (y : ℝ) :
    y * p.derivative.eval y =
      ∑ k : Fin (p.natDegree + 1), p.coeff k * (k : ℝ) * y ^ (k : ℕ) := by
  have he := congrArg (fun q : ℝ[X] => y * q.derivative.eval y) p.as_sum_range
  rw [he]
  simp only [Polynomial.derivative_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  have hm (k : ℕ) : y * ((monomial k) (p.coeff k)).derivative.eval y =
      p.coeff k * (k : ℝ) * y ^ k := by
    cases k with
    | zero => simp
    | succ k => simp [pow_succ]; ring
  simp only [hm, Finset.sum_range]

lemma polynomial_eval_exp (p : ℝ[X]) (x : ℝ) :
    p.eval (Real.exp (-x)) = ∑ k : Fin (p.natDegree + 1),
      p.coeff k * Real.exp (-(k : ℝ) * x) := by
  rw [Polynomial.eval_eq_sum_range]
  simp only [← Real.exp_nat_mul, Finset.sum_range, mul_neg, neg_mul]

lemma polynomial_euler_exp (p : ℝ[X]) (x : ℝ) :
    Real.exp (-x) * p.derivative.eval (Real.exp (-x)) =
      ∑ k : Fin (p.natDegree + 1), p.coeff k * (k : ℝ) * Real.exp (-(k : ℝ) * x) := by
  rw [polynomial_euler_eval]
  simp only [← Real.exp_nat_mul, mul_neg, neg_mul]

abbrev PolynomialIndex (p : ι → ℝ[X]) := ∀ i, Fin ((p i).natDegree + 1)

def polynomialWeight (p : ι → ℝ[X]) (k : PolynomialIndex p) : ℝ :=
  ∏ i, (p i).coeff (k i)

def exponentVector {p : ι → ℝ[X]} (k : PolynomialIndex p) : ι → ℝ := fun i => (k i : ℝ)

def mixedMultiplier {p : ι → ℝ[X]} (k : PolynomialIndex p) (S : Finset ι) : ℝ :=
  ∏ i ∈ S, (k i : ℝ)

noncomputable def mixedPolynomial (p : ι → ℝ[X]) (S : Finset ι) (x : ι → ℝ) : ℝ :=
  ∏ i, if i ∈ S then Real.exp (-x i) * (p i).derivative.eval (Real.exp (-x i))
    else (p i).eval (Real.exp (-x i))

lemma mixedPolynomial_expansion (p : ι → ℝ[X]) (S : Finset ι) (x : ι → ℝ) :
    mixedPolynomial p S x = ∑ k : PolynomialIndex p,
      polynomialWeight p k * mixedMultiplier k S * laplaceKernel (exponentVector k) x := by
  have hf (i : ι) :
      (if i ∈ S then Real.exp (-x i) * (p i).derivative.eval (Real.exp (-x i))
        else (p i).eval (Real.exp (-x i))) =
      ∑ k : Fin ((p i).natDegree + 1), (p i).coeff k *
        (if i ∈ S then (k : ℝ) else 1) * Real.exp (-(k : ℝ) * x i) := by
    split_ifs with hi
    · exact polynomial_euler_exp _ _
    · simpa only [mul_one] using polynomial_eval_exp (p i) (x i)
  rw [mixedPolynomial]
  simp_rw [hf]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter,
    polynomialWeight, mixedMultiplier, laplaceKernel, exponentVector,
    ← Real.exp_sum, Finset.sum_neg_distrib, neg_mul]

lemma mixedPolynomial_nonneg (p : ι → ℝ[X]) (S : Finset ι)
    (hp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).eval y)
    (hdp : ∀ i y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ (p i).derivative.eval y)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ mixedPolynomial p S x := by
  apply Finset.prod_nonneg
  intro i _
  have hy : Real.exp (-x i) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hx i))⟩
  split_ifs
  · exact mul_nonneg (Real.exp_pos _).le (hdp i _ hy)
  · exact hp i _ hy

lemma integrable_mixedPolynomial {μ : Measure (ι → ℝ)} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) (p : ι → ℝ[X]) (S : Finset ι) :
    Integrable (mixedPolynomial p S) μ := by
  simp_rw [show mixedPolynomial p S = fun x => ∑ k : PolynomialIndex p,
      polynomialWeight p k * mixedMultiplier k S * laplaceKernel (exponentVector k) x
    from funext (mixedPolynomial_expansion p S)]
  apply integrable_finsetSum
  intro k _
  exact (integrable_laplaceKernel hμ (fun i => by simp [exponentVector])).const_mul _

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def royenCoefficient (p : ι → Bool) (R : Matrix ι ι ℝ)
    (S : Finset ι) (t : ℝ) : ℝ :=
  -(deriv (fun u => ((interpolate p R u).submatrix
    (Subtype.val : S → ι) Subtype.val).det) t) / 2

noncomputable def polynomialExpectation (p : ι → ℝ[X]) (R : Matrix ι ι ℝ) : ℝ :=
  ∑ k : PolynomialIndex p, polynomialWeight p k *
    (Real.sqrt (diagonal (exponentVector k) * R + 1).det)⁻¹

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Polynomial _root_.Filter
open scoped unitInterval Topology

noncomputable def bernsteinP (n : ℕ) (a : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (a k) * bernsteinPolynomial ℝ n k

lemma bernsteinP_derivative (n : ℕ) (a : ℕ → ℝ) :
    (bernsteinP (n + 1) a).derivative =
      C (n + 1 : ℝ) * ∑ k ∈ Finset.range (n + 1),
        C (a (k + 1) - a k) * bernsteinPolynomial ℝ n k := by
  have hend : bernsteinPolynomial ℝ n (n + 1) = 0 := by
    simp [bernsteinPolynomial]
  have ht : (∑ k ∈ Finset.range (n + 1), C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), C (a k) * bernsteinPolynomial ℝ n k) -
        C (a 0) * bernsteinPolynomial ℝ n 0 := by
    have he := Finset.sum_range_succ' (fun k => C (a k) * bernsteinPolynomial ℝ n k) (n+1)
    rw [Finset.sum_range_succ, hend, mul_zero, add_zero] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  rw [bernsteinP, Finset.sum_range_succ']
  simp only [Polynomial.derivative_sum,
    Polynomial.derivative_C_mul, bernsteinPolynomial.derivative_succ_aux,
    bernsteinPolynomial.derivative_zero, Nat.add_sub_cancel,
    map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
  simp only [mul_sub, Finset.sum_sub_distrib, map_sub]
  simp only [show ∀ k, C (a (k + 1)) * ((n + 1) * bernsteinPolynomial ℝ n k) =
    (n + 1) * (C (a (k + 1)) * bernsteinPolynomial ℝ n k) from fun k => by ring,
    show ∀ k, C (a (k + 1)) * ((n + 1) * bernsteinPolynomial ℝ n (k + 1)) =
    (n + 1) * (C (a (k + 1)) * bernsteinPolynomial ℝ n (k + 1)) from fun k => by ring,
    ← Finset.mul_sum, ht]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

lemma bernsteinP_eval (n : ℕ) (f : C(ℝ, ℝ)) (x : I) :
    (bernsteinP n (fun k => f ((k : ℝ) / n))).eval (x : ℝ) =
      bernsteinApproximation n (f.comp ⟨Subtype.val, continuous_subtype_val⟩) x := by
  simp only [bernsteinP, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, bernsteinApproximation.apply, smul_eq_mul, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, bernstein.z, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]
  rfl

lemma bernsteinP_eval_nonneg (n : ℕ) (f : C(ℝ, ℝ))
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (bernsteinP n (fun k => f ((k : ℝ) / n))).eval x := by
  have he := bernsteinP_eval n f ⟨x, hx⟩
  rw [he, bernsteinApproximation.apply]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg bernstein_nonneg (hf _ (bernstein.z k).prop)

lemma bernsteinP_eval_le_one (n : ℕ) (f : C(ℝ, ℝ))
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (bernsteinP n (fun k => f ((k : ℝ) / n))).eval x ≤ 1 := by
  have he := bernsteinP_eval n f ⟨x, hx⟩
  rw [he, bernsteinApproximation.apply, ← bernstein.probability n ⟨x, hx⟩]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_of_le_one_right bernstein_nonneg (hf _ (bernstein.z k).prop)

lemma bernsteinP_derivative_nonneg (n : ℕ) (f : C(ℝ, ℝ))
    (hf : MonotoneOn f (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (bernsteinP n (fun k => f ((k : ℝ) / n))).derivative.eval x := by
  cases n with
  | zero => simp [bernsteinP, bernsteinPolynomial]
  | succ n =>
    rw [bernsteinP_derivative]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro k hk
    have hk' : k < n + 1 := Finset.mem_range.mp hk
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hk0 : (0 : ℝ) ≤ k / (n + 1) := div_nonneg (Nat.cast_nonneg _) hn.le
    have hk1 : (k : ℝ) / (n + 1) ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hk'.le)
    have hks0 : (0 : ℝ) ≤ (k + 1) / (n + 1) := by positivity
    have hks1 : (k + 1 : ℝ) / (n + 1) ≤ 1 :=
      (div_le_one hn).mpr (by exact_mod_cast hk')
    have hmono := hf ⟨hk0, hk1⟩ ⟨hks0, hks1⟩ (by gcongr; linarith)
    apply mul_nonneg
    · simpa only [Nat.cast_add, Nat.cast_one] using sub_nonneg.mpr hmono
    · exact @bernstein_nonneg n k ⟨x, hx⟩

lemma bernsteinP_tendsto (f : C(ℝ, ℝ)) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n => (bernsteinP n (fun k => f ((k : ℝ) / n))).eval x)
      atTop (𝓝 (f x)) := by
  simp_rw [bernsteinP_eval _ _ ⟨x, hx⟩]
  exact (continuous_eval_const ⟨x, hx⟩).continuousAt.tendsto.comp
    (bernsteinApproximation_uniform (f.comp ⟨Subtype.val, continuous_subtype_val⟩))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory Polynomial _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma interpolate_zero_posSemidef (b : ι → Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) : (interpolate b R 0).PosSemidef := by
  let A : Matrix ι ι ℝ := diagonal (fun i => if b i = true then 1 else 0)
  let B : Matrix ι ι ℝ := diagonal (fun i => if b i = true then 0 else 1)
  have he : interpolate b R 0 = A * R * Aᴴ + B * R * Bᴴ := by
    ext i j
    simp only [interpolate, zero_mul, A, B, diagonal_conjTranspose,
      star_trivial, diagonal_mul, mul_diagonal, Matrix.add_apply]
    cases b i <;> cases b j <;> simp
  rw [he]
  exact (hR.mul_mul_conjTranspose_same A).add (hR.mul_mul_conjTranspose_same B)

omit [Fintype ι] [DecidableEq ι] in
lemma interpolate_continuous (b : ι → Bool) (t : ℝ) :
    Continuous (fun R : Matrix ι ι ℝ => interpolate b R t) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  dsimp only [interpolate]
  split_ifs <;> fun_prop

lemma polynomialExpectation_continuousAt (p : ι → ℝ[X]) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) : ContinuousAt (polynomialExpectation p) R := by
  unfold polynomialExpectation
  apply tendsto_finsetSum
  intro k _
  apply ContinuousAt.const_mul
  apply ContinuousAt.inv₀
  · exact (Continuous.sqrt (by fun_prop)).continuousAt
  · exact (Real.sqrt_pos.mpr (det_diagonal_mul_add_one_pos hR
      (fun i => Nat.cast_nonneg (k i).val))).ne'

noncomputable def continuousProduct (f : ι → C(ℝ, ℝ)) (x : ι → ℝ) : ℝ :=
  ∏ i, f i (Real.exp (-x i))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def upperCutoff (n : ℕ) (a : ℝ) : C(ℝ, ℝ) :=
  ⟨fun y => min 1 (max 0 (1 + ((n : ℝ) + 1) * (y - a))), by fun_prop⟩

lemma upperCutoff_bounds (n : ℕ) (a y : ℝ) :
    upperCutoff n a y ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma upperCutoff_monotone (n : ℕ) (a : ℝ) : Monotone (upperCutoff n a) := by
  intro x y hxy
  dsimp only [upperCutoff, ContinuousMap.coe_mk]
  gcongr

lemma upperCutoff_tendsto (a y : ℝ) :
    Tendsto (fun n => upperCutoff n a y) atTop (𝓝 (if a ≤ y then (1 : ℝ) else 0)) := by
  by_cases h : a ≤ y
  · have he (n : ℕ) : upperCutoff n a y = 1 := by
      apply min_eq_left
      exact (by nlinarith [show (0 : ℝ) ≤ n by positivity] : (1:ℝ) ≤
        1 + ((n : ℝ)+1) * (y-a)) |>.trans (le_max_right _ _)
    simp only [he, ite_eq_left h]
    exact tendsto_const_nhds
  · have ha : 0 < a - y := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (a - y))
    have he : ∀ᶠ n : ℕ in atTop, upperCutoff n a y = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hb : 1 ≤ ((n : ℝ) + 1) * (a-y) := by
        have := (div_lt_iff₀ ha).mp hN
        nlinarith
      simp only [upperCutoff, ContinuousMap.coe_mk]
      rw [max_eq_left (by nlinarith), min_eq_right zero_le_one]
    simp only [ite_eq_right h]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

noncomputable def exponentialBox (a : ι → ℝ) : Set (ι → ℝ) :=
  {x | ∀ i, a i ≤ Real.exp (-x i)}

omit [DecidableEq ι] in
lemma measurableSet_exponentialBox (a : ι → ℝ) : MeasurableSet (exponentialBox a) := by
  unfold exponentialBox
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (by fun_prop))

omit [DecidableEq ι] in
lemma cutoffProduct_tendsto (a x : ι → ℝ) :
    Tendsto (fun n => continuousProduct (fun i => upperCutoff n (a i)) x) atTop
      (𝓝 ((exponentialBox a).indicator (fun _ => (1 : ℝ)) x)) := by
  have ht := tendsto_finsetProd Finset.univ
    (fun i _ => upperCutoff_tendsto (a i) (Real.exp (- x i)))
  convert ht using 1
  congr 1
  by_cases h : x ∈ exponentialBox a
  · rw [Set.indicator_of_mem h]
    have hi (i : ι) : a i ≤ Real.exp (-x i) := h i
    simp [hi]
  · rw [Set.indicator_of_notMem h]
    have hi : ∃ i, ¬ a i ≤ Real.exp (-x i) := by simpa [exponentialBox] using h
    obtain ⟨i, hi⟩ := hi
    symm
    exact congrArg nhds (Finset.prod_eq_zero (f := fun j => if a j ≤ Real.exp (-x j) then (1 : ℝ) else 0)
      (Finset.mem_univ i) (ite_eq_right hi))

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def coordinatePi (f : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (f i))

noncomputable def coordinateCLM (f : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.toContinuousLinearMap.comp
    (coordinatePi f)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma coordinateCLM_apply (f : κ → ι) (x : EuclideanSpace ℝ ι) (i : κ) :
    coordinateCLM f x i = x (f i) := rfl

lemma map_coordinate_multivariateGaussian (f : κ → ι) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) :
    (multivariateGaussian 0 R).map (coordinateCLM f) =
      multivariateGaussian 0 (R.submatrix f f) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian, map_zero]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have he (i : κ) : (fun u => ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, u⟫) ∘
        coordinateCLM f = fun u => u (f i) := by
      ext u
      simp [PiLp.inner_apply]
    simp_rw [he, covariance_eval_multivariateGaussian hR,
      covarianceBilin_multivariateGaussian (hR.submatrix _)]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma block_submatrix_eq (b : ι → Bool) (v : Bool) (R : Matrix ι ι ℝ) :
    (interpolate b R 0).submatrix (fun i : {i // b i = v} => i.val)
      (fun i : {i // b i = v} => i.val) =
        R.submatrix (fun i : {i // b i = v} => i.val) (fun i : {i // b i = v} => i.val) := by
  ext i j
  simp [Matrix.submatrix, interpolate, i.prop, j.prop]

omit [Fintype κ] [DecidableEq κ] in
lemma gaussian_blocks_independent (b : ι → Bool) {R : Matrix ι ι ℝ} (hR : R.PosSemidef) :
    IndepFun (coordinatePi (fun i : {i // b i = true} => i.val))
      (coordinatePi (fun i : {i // b i = false} => i.val))
        (multivariateGaussian 0 (interpolate b R 0)) := by
  apply HasGaussianLaw.indepFun_of_covariance_eval
  · exact IsGaussian.hasGaussianLaw_id.map
      ((coordinatePi (fun i : {i // b i = true} => i.val)).prod
        (coordinatePi (fun i : {i // b i = false} => i.val)))
  · intro i j
    change cov[fun x => x i.val, fun x => x j.val;
      multivariateGaussian 0 (interpolate b R 0)] = 0
    rw [covariance_eval_multivariateGaussian (interpolate_zero_posSemidef b hR)]
    simp [interpolate, i.prop, j.prop]

noncomputable def quadraticBox (t : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, x i ^ 2 / 2 ≤ t i}

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma measurableSet_quadraticBox (t : ι → ℝ) : MeasurableSet (quadraticBox t) := by
  unfold quadraticBox
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)

omit [Fintype κ] [DecidableEq κ] in
lemma squareLaw_exponentialBox (R : Matrix ι ι ℝ) (t : ι → ℝ) :
    (squareLaw R).real (exponentialBox (fun i => Real.exp (-t i))) =
      (multivariateGaussian 0 R).real (quadraticBox t) := by
  unfold Measure.real squareLaw
  rw [Measure.map_apply (by fun_prop) (measurableSet_exponentialBox _)]
  congr 2
  ext x
  simp [exponentialBox, quadraticBox, Real.exp_le_exp]

omit [Fintype κ] [DecidableEq κ] in
lemma block_marginal_eq (b : ι → Bool) (v : Bool) {R : Matrix ι ι ℝ}
    (hR : R.PosSemidef) (S : Set (EuclideanSpace ℝ {i // b i = v})) (hS : MeasurableSet S) :
    (multivariateGaussian 0 (interpolate b R 0)) ((coordinateCLM Subtype.val) ⁻¹' S) =
      (multivariateGaussian 0 R) ((coordinateCLM Subtype.val) ⁻¹' S) := by
  rw [← Measure.map_apply (coordinateCLM Subtype.val).measurable hS,
    ← Measure.map_apply (coordinateCLM Subtype.val).measurable hS,
    map_coordinate_multivariateGaussian _ (interpolate_zero_posSemidef b hR),
    map_coordinate_multivariateGaussian _ hR, block_submatrix_eq]

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def innerCoordinates (u : ι → E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (u i)))

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma innerCoordinates_apply (u : ι → E) (x : E) (i : ι) :
    innerCoordinates u x i = ⟪u i, x⟫ := rfl

lemma map_innerCoordinates_stdGaussian (u : ι → E) :
    (stdGaussian E).map (innerCoordinates u) = multivariateGaussian 0 (gram ℝ u) := by
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, map_zero]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have he (i : ι) : (fun y => ⟪(EuclideanSpace.basisFun ι ℝ).toBasis i, y⟫) ∘
        innerCoordinates u = fun x => ⟪u i, x⟫ := by
      ext x
      simp [PiLp.inner_apply]
    simp_rw [he]
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian (posSemidef_gram ℝ u)]
    simp
    rfl
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter InnerProductSpace
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma closed_symmetric_convex_countable_slabs {K : Set E} (hK : IsClosed K)
    (hc : Convex ℝ K) (hs : ∀ x ∈ K, -x ∈ K) (h0 : (0:E) ∈ K) :
    ∃ (u : ℕ → E) (r : ℕ → ℝ), (∀ n, 0 ≤ r n) ∧
      K = ⋂ n, {x | |⟪u n, x⟫| ≤ r n} := by
  let I := {p : StrongDual ℝ E × ℝ // ∀ x ∈ K, |p.1 x| ≤ p.2}
  let : Nonempty I := ⟨⟨(0, 0), by intro x _; simp⟩⟩
  let U (p : I) : Set E := {x | |p.val.1 x| ≤ p.val.2}ᶜ
  have ho (p : I) : IsOpen (U p) := (isClosed_le (p.val.1.continuous.abs) continuous_const).isOpen_compl
  have hcover : Kᶜ ⊆ ⋃ p, U p := by
    intro x hx
    obtain ⟨f, r, hf, hr⟩ := geometric_hahn_banach_closed_point hc hK hx
    have hb : ∀ y ∈ K, |f y| ≤ r := by
      intro y hy
      apply abs_le.mpr
      have hneg := hf (-y) (hs y hy)
      simp only [map_neg] at hneg
      exact ⟨by linarith, (hf y hy).le⟩
    refine Set.mem_iUnion.mpr ⟨⟨(f, r), hb⟩, ?_⟩
    change ¬ |f x| ≤ r
    exact not_le.mpr (lt_of_lt_of_le hr (le_abs_self _))
  obtain ⟨g, hg⟩ := (HereditarilyLindelofSpace.isLindelof Kᶜ).indexed_countable_subcover U ho hcover
  refine ⟨fun n => (toDual ℝ E).symm (g n).val.1, fun n => (g n).val.2, ?_, ?_⟩
  · intro n
    simpa using (g n).prop 0 h0
  · ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, toDual_symm_apply]
    constructor
    · exact fun hx n => (g n).prop x hx
    · intro hx
      by_contra hn
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hg hn)
      exact hn (hx n)

noncomputable def partialSlabs (u : ℕ → E) (r : ℕ → ℝ) (n : ℕ) : Set E :=
  {x | ∀ i, i < n → |⟪u i, x⟫| ≤ r i}

omit [FiniteDimensional ℝ E] in
lemma measurableSet_partialSlabs (u : ℕ → E) (r : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (partialSlabs u r n) := by
  unfold partialSlabs
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_le (by fun_prop) measurable_const))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma partialSlabs_antitone (u : ℕ → E) (r : ℕ → ℝ) : Antitone (partialSlabs u r) := by
  intro n m hnm x hx i hi
  exact hx i (hi.trans_le hnm)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma partialSlabs_iInter (u : ℕ → E) (r : ℕ → ℝ) :
    (⋂ n, partialSlabs u r n) = ⋂ n, {x | |⟪u n, x⟫| ≤ r n} := by
  ext x
  simp only [Set.mem_iInter, partialSlabs, Set.mem_ofPred_eq]
  constructor
  · exact fun h i => h (i+1) i (Nat.lt_succ_self i)
  · exact fun h _ i _ => h i

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma tendsto_real_measure_decreasing {μ : Measure E} [IsFiniteMeasure μ] {S : ℕ → Set E}
    (hS : ∀ n, MeasurableSet (S n)) (hm : Antitone S) :
    Tendsto (fun n => μ.real (S n)) atTop (𝓝 (μ.real (⋂ n, S n))) := by
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
    (tendsto_measure_iInter_atTop (fun n => (hS n).nullMeasurableSet) hm
      ⟨0, measure_ne_top _ _⟩)

end EuclideanSteinitz.GaussianCorrelation

namespace EuclideanSteinitz.GaussianCorrelation
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
