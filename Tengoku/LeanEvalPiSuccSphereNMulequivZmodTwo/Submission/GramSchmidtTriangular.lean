import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SOGramSchmidtSmooth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The triangular factor of rowwise Gram--Schmidt

`Submission.matrixGramSchmidtSO` (`SOGramSchmidtSmooth.lean`) sends a matrix of
positive determinant to the special-orthogonal matrix whose rows are the
normalized Gram--Schmidt orthonormalization of its rows.  This file supplies
the *other* factor of that decomposition and its two structural properties.

For a linearly independent family `v` of Euclidean vectors put

`gsLower v = rowsMatrix v * (rowsMatrix (gramSchmidtNormed ℝ v))ᵀ`,

so that `rowsMatrix v = gsLower v * rowsMatrix (gramSchmidtNormed ℝ v)`
(`rowsMatrix_eq_gsLower_mul`).  Then

* `gsLower_eq_zero_of_lt` — `gsLower v` is **lower triangular**;
* `gsLower_diag` — its diagonal entries are `‖gramSchmidt ℝ v i‖ > 0`.

Two consequences are what the rest of the development uses.

* `det_gsInterp_pos` / `linearIndependent_frameInterp` /
  `det_rowsMatrix_frameInterp_pos`: the straight-line homotopy
  `s ↦ (1 - s) • v + s • gramSchmidtNormed ℝ v` from a positively oriented
  basis to its own orthonormalization stays a positively oriented basis, because
  in the Gram--Schmidt gauge its matrix is `(1 - s) • gsLower v + s • 1`, again
  lower triangular with positive diagonal.  This is the deformation that
  identifies the frame-comparison loop of two presentations with the loop of
  their transition matrices.

* `matrixGramSchmidtSO_mul_orthogonal`: rowwise Gram--Schmidt is
  **equivariant on the right** under the orthogonal group, `Q(M * O) = Q(M) * O`.
  This is proved from the corresponding statement for `gramSchmidt` along a
  linear isometry, `gramSchmidt_comp_isometry`.

Nothing here depends on level sets; everything is linear algebra.
-/

set_option autoImplicit false

noncomputable section

namespace Submission
namespace GramSchmidtTriangular

open Matrix InnerProductSpace
open scoped RealInnerProductSpace ContDiff Matrix

variable {k : ℕ}

/-! ## The orthonormal factor -/

/-- The normalized Gram--Schmidt row matrix is orthogonal.-/
theorem rows_mul_transpose_gramSchmidtNormed
    {v : Fin k → EuclideanSpace ℝ (Fin k)} (hv : LinearIndependent ℝ v) :
    rowsMatrix (gramSchmidtNormed ℝ v) * (rowsMatrix (gramSchmidtNormed ℝ v))ᵀ
      = 1 := by
  have horthonormal : Orthonormal ℝ (gramSchmidtNormed ℝ v) :=
    gramSchmidtNormed_orthonormal hv
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hentries : ∀ l, rowsMatrix (gramSchmidtNormed ℝ v) i l *
      (rowsMatrix (gramSchmidtNormed ℝ v))ᵀ l j =
      (gramSchmidtNormed ℝ v i) l * (gramSchmidtNormed ℝ v j) l := by
    intro l
    rw [Matrix.transpose_apply]
    rfl
  rw [Finset.sum_congr rfl fun l _ => hentries l]
  have hinner := orthonormal_iff_ite.mp horthonormal i j
  rw [PiLp.inner_apply] at hinner
  simp only [RCLike.inner_apply, conj_trivial] at hinner
  rw [← hinner]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem transpose_mul_rows_gramSchmidtNormed
    {v : Fin k → EuclideanSpace ℝ (Fin k)} (hv : LinearIndependent ℝ v) :
    (rowsMatrix (gramSchmidtNormed ℝ v))ᵀ * rowsMatrix (gramSchmidtNormed ℝ v)
      = 1 :=
  mul_eq_one_comm.mp (rows_mul_transpose_gramSchmidtNormed hv)

/-! ## Orthogonality against the earlier Gram--Schmidt vectors -/

/-- Every vector in the span of the earlier Gram--Schmidt vectors is orthogonal
to the current one.-/
theorem inner_eq_zero_of_mem_span_gramSchmidt_Iio
    {v : Fin k → EuclideanSpace ℝ (Fin k)} {j : Fin k}
    {w : EuclideanSpace ℝ (Fin k)}
    (hw : w ∈ Submodule.span ℝ (gramSchmidt ℝ v '' Set.Iio j)) :
    ⟪w, gramSchmidt ℝ v j⟫ = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact gramSchmidt_orthogonal ℝ v (ne_of_lt hl)
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [real_inner_smul_left, hx, mul_zero]

/-- An earlier member of the family is orthogonal to a later Gram--Schmidt
vector.-/
theorem inner_gramSchmidt_eq_zero_of_lt
    {v : Fin k → EuclideanSpace ℝ (Fin k)} {i j : Fin k} (hij : i < j) :
    ⟪v i, gramSchmidt ℝ v j⟫ = 0 := by
  apply inner_eq_zero_of_mem_span_gramSchmidt_Iio
  rw [span_gramSchmidt_Iio ℝ v j]
  exact Submodule.subset_span ⟨i, hij, rfl⟩

/-- The Gram--Schmidt correction is orthogonal to the corrected vector.-/
theorem inner_self_gramSchmidt (v : Fin k → EuclideanSpace ℝ (Fin k))
    (i : Fin k) :
    ⟪v i, gramSchmidt ℝ v i⟫ = ‖gramSchmidt ℝ v i‖ ^ 2 := by
  have hzero : ⟪gramSchmidt ℝ v i - v i, gramSchmidt ℝ v i⟫ = 0 :=
    inner_eq_zero_of_mem_span_gramSchmidt_Iio (gramSchmidt_sub_mem_span v i)
  rw [inner_sub_left] at hzero
  have hself : ⟪gramSchmidt ℝ v i, gramSchmidt ℝ v i⟫ = ‖gramSchmidt ℝ v i‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  rw [hself] at hzero
  linarith

/-! ## The lower-triangular factor -/

/-- The triangular factor of the rowwise Gram--Schmidt decomposition.-/
def gsLower (v : Fin k → EuclideanSpace ℝ (Fin k)) :
    Matrix (Fin k) (Fin k) ℝ :=
  rowsMatrix v * (rowsMatrix (gramSchmidtNormed ℝ v))ᵀ

theorem gsLower_apply (v : Fin k → EuclideanSpace ℝ (Fin k)) (i j : Fin k) :
    gsLower v i j = ⟪v i, gramSchmidtNormed ℝ v j⟫ := by
  rw [gsLower, Matrix.mul_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- **The Gram--Schmidt factor is lower triangular.**-/
theorem gsLower_eq_zero_of_lt (v : Fin k → EuclideanSpace ℝ (Fin k))
    {i j : Fin k} (hij : i < j) : gsLower v i j = 0 := by
  rw [gsLower_apply, gramSchmidtNormed, real_inner_smul_right,
    inner_gramSchmidt_eq_zero_of_lt hij, mul_zero]

/-- **The diagonal of the Gram--Schmidt factor.**-/
theorem gsLower_diag {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) (i : Fin k) :
    gsLower v i i = ‖gramSchmidt ℝ v i‖ := by
  have hne : gramSchmidt ℝ v i ≠ 0 := gramSchmidt_ne_zero i hv
  have hpos : 0 < ‖gramSchmidt ℝ v i‖ := norm_pos_iff.mpr hne
  rw [gsLower_apply, gramSchmidtNormed, real_inner_smul_right,
    inner_self_gramSchmidt]
  have key : (‖gramSchmidt ℝ v i‖)⁻¹ * ‖gramSchmidt ℝ v i‖ ^ 2
      = ‖gramSchmidt ℝ v i‖ := by
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
  exact key

theorem gsLower_diag_pos {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) (i : Fin k) : 0 < gsLower v i i := by
  rw [gsLower_diag hv i]
  exact norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)

/-- **The rowwise Gram--Schmidt factorization.**-/
theorem rowsMatrix_eq_gsLower_mul {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) :
    rowsMatrix v = gsLower v * rowsMatrix (gramSchmidtNormed ℝ v) := by
  rw [gsLower, Matrix.mul_assoc, transpose_mul_rows_gramSchmidtNormed hv,
    Matrix.mul_one]

/-! ## The straight-line deformation onto the orthonormalized frame -/

/-- The interpolating triangular matrix.-/
def gsInterp (v : Fin k → EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (1 - s) • gsLower v + s • (1 : Matrix (Fin k) (Fin k) ℝ)

theorem gsInterp_eq_zero_of_lt (v : Fin k → EuclideanSpace ℝ (Fin k)) (s : ℝ)
    {i j : Fin k} (hij : i < j) : gsInterp v s i j = 0 := by
  have hone : (1 : Matrix (Fin k) (Fin k) ℝ) i j = 0 :=
    Matrix.one_apply_ne (ne_of_lt hij)
  simp [gsInterp, gsLower_eq_zero_of_lt v hij, hone]

theorem gsInterp_diag {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) (s : ℝ) (i : Fin k) :
    gsInterp v s i i = (1 - s) * ‖gramSchmidt ℝ v i‖ + s := by
  simp [gsInterp, gsLower_diag hv i, Matrix.one_apply_eq]

/-- **The interpolating triangular matrix has positive determinant.**-/
theorem det_gsInterp_pos {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (gsInterp v s).det := by
  rw [Matrix.det_of_isLowerTriangular _ (fun i j hij => gsInterp_eq_zero_of_lt v s hij)]
  apply Finset.prod_pos
  intro i _
  rw [gsInterp_diag hv s i]
  have hpos : 0 < ‖gramSchmidt ℝ v i‖ := norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)
  rcases eq_or_lt_of_le hs1 with heq | hlt
  · subst heq; norm_num
  · have h1 : 0 < (1 - s) * ‖gramSchmidt ℝ v i‖ := mul_pos (by linarith) hpos
    linarith

/-- The straight-line deformation of a frame onto its orthonormalization.-/
def frameInterp (v : Fin k → EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    Fin k → EuclideanSpace ℝ (Fin k) :=
  fun i => (1 - s) • v i + s • gramSchmidtNormed ℝ v i

@[simp] theorem frameInterp_zero (v : Fin k → EuclideanSpace ℝ (Fin k)) :
    frameInterp v 0 = v := by
  funext i; simp [frameInterp]

@[simp] theorem frameInterp_one (v : Fin k → EuclideanSpace ℝ (Fin k)) :
    frameInterp v 1 = gramSchmidtNormed ℝ v := by
  funext i; simp [frameInterp]

theorem rowsMatrix_frameInterp {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) (s : ℝ) :
    rowsMatrix (frameInterp v s)
      = gsInterp v s * rowsMatrix (gramSchmidtNormed ℝ v) := by
  have hsplit : rowsMatrix (frameInterp v s)
      = (1 - s) • rowsMatrix v + s • rowsMatrix (gramSchmidtNormed ℝ v) := by
    ext i j
    rfl
  rw [hsplit, gsInterp, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, ← rowsMatrix_eq_gsLower_mul hv]

/-- **The straight-line deformation stays a positively oriented basis.**-/
theorem det_rowsMatrix_frameInterp_pos {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) (hdet : 0 < (rowsMatrix v).det)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 < (rowsMatrix (frameInterp v s)).det := by
  have hQ : 0 < (rowsMatrix (gramSchmidtNormed ℝ v)).det := by
    rw [det_rowsMatrix_gramSchmidtNormed]
    apply mul_pos
    · apply Finset.prod_pos
      intro i _
      have hpos : 0 < ‖gramSchmidt ℝ v i‖ :=
        norm_pos_iff.mpr (gramSchmidt_ne_zero i hv)
      positivity
    · exact hdet
  rw [rowsMatrix_frameInterp hv s, Matrix.det_mul]
  exact mul_pos (det_gsInterp_pos hv hs0 hs1) hQ

theorem linearIndependent_frameInterp {v : Fin k → EuclideanSpace ℝ (Fin k)}
    (hv : LinearIndependent ℝ v) (hdet : 0 < (rowsMatrix v).det)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    LinearIndependent ℝ (frameInterp v s) := by
  have h := det_rowsMatrix_frameInterp_pos hv hdet hs0 hs1
  have := linearIndependent_matrixRows_of_det_ne_zero (ne_of_gt h)
  rwa [show matrixRows (rowsMatrix (frameInterp v s)) = frameInterp v s from rfl] at this

/-! ## Right equivariance of Gram--Schmidt under isometries -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Gram--Schmidt commutes with a linear isometry.**-/
theorem gramSchmidt_comp_isometry (f : E →ₗᵢ[ℝ] E) (v : Fin k → E) (i : Fin k) :
    gramSchmidt ℝ (fun j => f (v j)) i = f (gramSchmidt ℝ v i) := by
  have key : ∀ N : ℕ, ∀ i : Fin k, (i : ℕ) = N →
      gramSchmidt ℝ (fun j => f (v j)) i = f (gramSchmidt ℝ v i) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro i hi
      rw [gramSchmidt_def ℝ (fun j => f (v j)) i, gramSchmidt_def ℝ v i,
        map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : (j : ℕ) < N := by
        have hji : j < i := Finset.mem_Iio.mp hj
        omega
      have hIH : gramSchmidt ℝ (fun l => f (v l)) j = f (gramSchmidt ℝ v j) :=
        IH (j : ℕ) hjN j rfl
      rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton,
        hIH, f.inner_map_map, f.norm_map, f.map_smul]
  exact key (i : ℕ) i rfl

theorem gramSchmidtNormed_comp_isometry (f : E →ₗᵢ[ℝ] E) (v : Fin k → E)
    (i : Fin k) :
    gramSchmidtNormed ℝ (fun j => f (v j)) i = f (gramSchmidtNormed ℝ v i) := by
  rw [gramSchmidtNormed, gramSchmidtNormed, gramSchmidt_comp_isometry f v i,
    f.norm_map, map_smul]

/-! ## Right equivariance of the rowwise Gram--Schmidt matrix -/

/-- The inner product of two Euclidean vectors as a dot product of their
coordinate tuples.-/
theorem inner_eq_dotProduct (a b : EuclideanSpace ℝ (Fin k)) :
    ⟪a, b⟫ = (WithLp.ofLp a) ⬝ᵥ (WithLp.ofLp b) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  show ∑ x, (WithLp.ofLp b) x * (WithLp.ofLp a) x
    = ∑ x, (WithLp.ofLp a) x * (WithLp.ofLp b) x
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem dotProduct_vecMul_of_mul_transpose {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q * Qᵀ = 1) (x y : Fin k → ℝ) :
    (x ᵥ* Q) ⬝ᵥ (y ᵥ* Q) = x ⬝ᵥ y := by
  rw [← Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    hQ, Matrix.one_mulVec]

/-- Right multiplication by a matrix, as a linear map on Euclidean space.-/
def rowVecMap (Q : Matrix (Fin k) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap ∘ₗ
    (Matrix.vecMulLinear Q) ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap

@[simp] theorem rowVecMap_apply (Q : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    rowVecMap Q x = WithLp.toLp 2 ((WithLp.ofLp x) ᵥ* Q) := rfl

/-- Right multiplication by an orthogonal matrix is a linear isometry.-/
def rowVecIsometry {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q * Qᵀ = 1) :
    EuclideanSpace ℝ (Fin k) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearMap.isometryOfInner (rowVecMap Q) <| by
    intro x y
    rw [rowVecMap_apply, rowVecMap_apply, inner_eq_dotProduct, inner_eq_dotProduct]
    exact dotProduct_vecMul_of_mul_transpose hQ _ _

@[simp] theorem rowVecIsometry_apply {Q : Matrix (Fin k) (Fin k) ℝ}
    (hQ : Q * Qᵀ = 1) (x : EuclideanSpace ℝ (Fin k)) :
    rowVecIsometry hQ x = WithLp.toLp 2 ((WithLp.ofLp x) ᵥ* Q) := rfl

theorem matrixRows_mul (M Q : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) :
    matrixRows (M * Q) i = WithLp.toLp 2 ((WithLp.ofLp (matrixRows M i)) ᵥ* Q) := by
  rfl

theorem rowsMatrix_rowVecMap (Q : Matrix (Fin k) (Fin k) ℝ)
    (w : Fin k → EuclideanSpace ℝ (Fin k)) :
    rowsMatrix (fun i => WithLp.toLp 2 ((WithLp.ofLp (w i)) ᵥ* Q))
      = rowsMatrix w * Q := by
  ext i j
  rfl

/-- **Rowwise Gram--Schmidt is right equivariant under the orthogonal group.**-/
theorem rowsMatrix_gramSchmidtNormed_matrixRows_mul
    {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Q * Qᵀ = 1)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    rowsMatrix (gramSchmidtNormed ℝ (matrixRows (M * Q)))
      = rowsMatrix (gramSchmidtNormed ℝ (matrixRows M)) * Q := by
  have hfam : (fun i => matrixRows (M * Q) i)
      = fun i => rowVecIsometry hQ (matrixRows M i) := by
    funext i
    rw [rowVecIsometry_apply]
    exact matrixRows_mul M Q i
  have hstep : ∀ i, gramSchmidtNormed ℝ (matrixRows (M * Q)) i
      = rowVecIsometry hQ (gramSchmidtNormed ℝ (matrixRows M) i) := by
    intro i
    rw [show (matrixRows (M * Q)) = fun i => rowVecIsometry hQ (matrixRows M i) from hfam]
    exact gramSchmidtNormed_comp_isometry (rowVecIsometry hQ) (matrixRows M) i
  rw [show gramSchmidtNormed ℝ (matrixRows (M * Q))
      = fun i => WithLp.toLp 2
        ((WithLp.ofLp (gramSchmidtNormed ℝ (matrixRows M) i)) ᵥ* Q) from
    funext hstep]
  exact rowsMatrix_rowVecMap Q (gramSchmidtNormed ℝ (matrixRows M))

end GramSchmidtTriangular
end Submission
