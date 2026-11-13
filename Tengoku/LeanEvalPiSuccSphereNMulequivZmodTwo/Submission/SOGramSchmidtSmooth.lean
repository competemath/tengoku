import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.LevelFrame
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SORotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Smooth Gram--Schmidt projection to the special orthogonal group

This file supplies the analytic retraction needed when a continuous
`SO(m)`-homotopy is first approximated in the ambient matrix space.  A smooth
family of positively oriented bases is sent, rowwise, to a smooth family in
`SO(m)` by normalized Gram--Schmidt.
-/

noncomputable section

open Matrix InnerProductSpace Submodule
open scoped ContDiff RealInnerProductSpace

namespace Submission

set_option autoImplicit false

/-- Gram--Schmidt depends smoothly on a smooth pointwise independent family
of finite frames.
@isnad1 id=contdiff.2h4v.s8.a58fa890c04d from=translated src=- shape=5a0ef55a vocab=0cc57018
-/
theorem contDiff_gramSchmidt_family
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {m : ℕ} {A : T → Fin m → EuclideanSpace ℝ (Fin m)}
    (hA : ∀ i, ContDiff ℝ ∞ fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t)) (i : Fin m) :
    ContDiff ℝ ∞ fun t => gramSchmidt ℝ (A t) i := by
  have key : ∀ N : ℕ, ∀ i : Fin m, (i : ℕ) = N →
      ContDiff ℝ ∞ fun t => gramSchmidt ℝ (A t) i := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro i hi
      have hrw : (fun t => gramSchmidt ℝ (A t) i) = fun t => A t i -
          ∑ j ∈ Finset.Iio i,
            (inner ℝ (gramSchmidt ℝ (A t) j) (A t i) /
              ((‖gramSchmidt ℝ (A t) j‖ : ℝ) ^ 2)) •
                gramSchmidt ℝ (A t) j := by
        funext t
        rw [gramSchmidt_def]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [starProjection_singleton]
        norm_num
      rw [hrw]
      apply (hA i).sub
      apply ContDiff.sum
      intro j hj
      have hjN : (j : ℕ) < N := by
        have hji : j < i := Finset.mem_Iio.mp hj
        omega
      have hgj : ContDiff ℝ ∞ fun t => gramSchmidt ℝ (A t) j :=
        IH (j : ℕ) hjN j rfl
      have hquot : ContDiff ℝ ∞ fun t =>
          inner ℝ (gramSchmidt ℝ (A t) j) (A t i) /
            ‖gramSchmidt ℝ (A t) j‖ ^ 2 := by
        apply ContDiff.div (ContDiff.inner ℝ hgj (hA i))
          (ContDiff.norm_sq ℝ hgj)
        intro t
        exact pow_ne_zero 2
          (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero j (hInd t)))
      exact hquot.smul hgj
  exact key (i : ℕ) i rfl

/-- Normalized Gram--Schmidt is smooth on smooth pointwise independent
families.
@isnad1 id=contdiff.2h4v.s8.99c8f898e398 from=translated src=- shape=5a0ef55a vocab=eb46b400
-/
theorem contDiff_gramSchmidtNormed_family
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {m : ℕ} {A : T → Fin m → EuclideanSpace ℝ (Fin m)}
    (hA : ∀ i, ContDiff ℝ ∞ fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t)) (i : Fin m) :
    ContDiff ℝ ∞ fun t => gramSchmidtNormed ℝ (A t) i := by
  have hgs := contDiff_gramSchmidt_family hA hInd i
  have hne : ∀ t, gramSchmidt ℝ (A t) i ≠ 0 := fun t =>
    gramSchmidt_ne_zero i (hInd t)
  have hnorm : ContDiff ℝ ∞ fun t => ‖gramSchmidt ℝ (A t) i‖⁻¹ :=
    (ContDiff.norm ℝ hgs hne).inv fun t => norm_ne_zero_iff.mpr (hne t)
  have heq : (fun t => gramSchmidtNormed ℝ (A t) i) =
      fun t => ‖gramSchmidt ℝ (A t) i‖⁻¹ • gramSchmidt ℝ (A t) i := by
    funext t
    rw [gramSchmidtNormed]
    norm_num
  rw [heq]
  exact hnorm.smul hgs

/-- Normalized Gram--Schmidt fixes an orthonormal frame pointwise.
@isnad1 id=eq.1h2v.s7.0bb4810ef35d from=translated src=- shape=16f95abf vocab=75e5dc22
-/
theorem gramSchmidtNormed_eq_of_orthonormal
    {m : ℕ} {v : Fin m → EuclideanSpace ℝ (Fin m)}
    (hv : Orthonormal ℝ v) :
    gramSchmidtNormed ℝ v = v := by
  funext i
  rw [gramSchmidtNormed, gramSchmidt_of_orthogonal ℝ hv.2, hv.1 i]
  simp

/-! ## Matrices as row frames -/

/-- Regard the rows of a real matrix as Euclidean vectors.-/
def matrixRows {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    Fin m → EuclideanSpace ℝ (Fin m) := fun i => WithLp.toLp 2 (M i)

/--
@isnad1 id=eq.0h2v.s4.f857f0392504 from=translated src=- shape=257a1ee2 vocab=f2a6dc93
-/
@[simp] theorem rowsMatrix_matrixRows {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) :
    rowsMatrix (matrixRows M) = M := by
  ext i j
  rfl

/-- Entrywise smoothness of a matrix family gives smoothness of every
Euclidean row.
@isnad1 id=contdiff.1h4v.s7.35919d007ece from=translated src=- shape=416b862d vocab=53e3caef
-/
theorem contDiff_matrixRows
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {m : ℕ} {M : T → Matrix (Fin m) (Fin m) ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ fun t => M t i j) (i : Fin m) :
    ContDiff ℝ ∞ fun t => matrixRows (M t) i := by
  have hrow : ContDiff ℝ ∞ fun t => M t i := by
    rw [contDiff_pi]
    exact hM i
  unfold matrixRows
  change ContDiff ℝ ∞ (WithLp.toLp 2 ∘ fun t => M t i)
  exact PiLp.contDiff_toLp.comp hrow

/-- A matrix with nonzero determinant has linearly independent Euclidean
rows.
@isnad1 id=linearin.1h2v.s6.542602a276b4 from=translated src=- shape=aca28702 vocab=aa14a504
-/
theorem linearIndependent_matrixRows_of_det_ne_zero
    {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ} (hdet : M.det ≠ 0) :
    LinearIndependent ℝ (matrixRows M) := by
  have hrow : LinearIndependent ℝ M.row := by
    rw [Matrix.linearIndependent_rows_iff_isUnit,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  have hiff :
      LinearIndependent ℝ (fun i => WithLp.ofLp (matrixRows M i)) ↔
        LinearIndependent ℝ (matrixRows M) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap.linearIndependent_iff
      (LinearEquiv.ker _)
  apply hiff.mp
  have hrow' : LinearIndependent ℝ (fun i => M i) := by
    rw [show (fun i => M i) = M.row by
      funext i j
      rfl]
    exact hrow
  rw [show (fun i => WithLp.ofLp (matrixRows M i)) = fun i => M i by
    funext i j
    rfl]
  exact hrow'

/-- The rows of an orthogonal matrix form an orthonormal Euclidean frame.
@isnad1 id=orthonor.1h2v.s7.a5f79e295158 from=translated src=- shape=9a622c00 vocab=4fea4f5e
-/
theorem orthonormal_matrixRows_of_mem_orthogonalGroup
    {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ}
    (hM : M ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    Orthonormal ℝ (matrixRows M) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  have hmul : M * Mᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mp hM
  have hij := congrArg (fun A : Matrix (Fin m) (Fin m) ℝ => A i j) hmul
  rw [Matrix.mul_apply, Matrix.one_apply] at hij
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, matrixRows,
    Matrix.transpose_apply] at hij ⊢
  rw [← hij]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Normalized Gram--Schmidt sends every positively oriented basis to a
special-orthogonal row matrix.
@isnad1 id=mem.2h2v.s8.64a95d350769 from=translated src=- shape=cb601249 vocab=9371ffd5
-/
theorem rowsMatrix_gramSchmidtNormed_mem_specialOrthogonalGroup
    {m : ℕ} {v : Fin m → EuclideanSpace ℝ (Fin m)}
    (hInd : LinearIndependent ℝ v)
    (hdet : 0 < (rowsMatrix v).det) :
    rowsMatrix (gramSchmidtNormed ℝ v) ∈
      Matrix.specialOrthogonalGroup (Fin m) ℝ := by
  have horthonormal : Orthonormal ℝ (gramSchmidtNormed ℝ v) :=
    gramSchmidtNormed_orthonormal hInd
  let Q := rowsMatrix (gramSchmidtNormed ℝ v)
  have hmul : Q * Qᵀ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hentries : ∀ k, Q i k * Qᵀ k j =
        (gramSchmidtNormed ℝ v i) k *
          (gramSchmidtNormed ℝ v j) k := by
      intro k
      rw [Matrix.transpose_apply]
      rfl
    rw [Finset.sum_congr rfl fun k _ => hentries k]
    have hinner := orthonormal_iff_ite.mp horthonormal i j
    rw [PiLp.inner_apply] at hinner
    simp only [RCLike.inner_apply, conj_trivial] at hinner
    rw [← hinner]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have horth : Q ∈ Matrix.orthogonalGroup (Fin m) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).mpr hmul
  have hdetpos : 0 < Q.det := by
    change 0 < (rowsMatrix (gramSchmidtNormed ℝ v)).det
    rw [det_rowsMatrix_gramSchmidtNormed]
    apply mul_pos
    · apply Finset.prod_pos
      intro i _
      have hne : gramSchmidt ℝ v i ≠ 0 := gramSchmidt_ne_zero i hInd
      have hnorm : 0 < ‖gramSchmidt ℝ v i‖ := norm_pos_iff.mpr hne
      positivity
    · exact hdet
  have hdetsq : Q.det * Q.det = 1 := by
    have h := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact h
  have hdetone : Q.det = 1 := by
    rcases mul_self_eq_one_iff.mp hdetsq with h | h
    · exact h
    · rw [h] at hdetpos
      linarith
  exact Matrix.mem_specialOrthogonalGroup_iff.mpr ⟨horth, hdetone⟩

/-- The smooth Gram--Schmidt projection of a family of positively oriented
bases into `SO(m)`.-/
def gramSchmidtSO
    {T : Type*} {m : ℕ}
    (A : T → Fin m → EuclideanSpace ℝ (Fin m))
    (hInd : ∀ t, LinearIndependent ℝ (A t))
    (hdet : ∀ t, 0 < (rowsMatrix (A t)).det) :
    T → SOGroup m := fun t =>
  ⟨rowsMatrix (gramSchmidtNormed ℝ (A t)),
    rowsMatrix_gramSchmidtNormed_mem_specialOrthogonalGroup
      (hInd t) (hdet t)⟩

/--
@isnad1 id=eq.2h4v.s8.ab385609e5d5 from=translated src=- shape=030e9367 vocab=62498949
-/
@[simp] theorem gramSchmidtSO_coe
    {T : Type*} {m : ℕ}
    (A : T → Fin m → EuclideanSpace ℝ (Fin m))
    (hInd : ∀ t, LinearIndependent ℝ (A t))
    (hdet : ∀ t, 0 < (rowsMatrix (A t)).det) (t : T) :
    ((gramSchmidtSO A hInd hdet t : SOGroup m) :
      Matrix (Fin m) (Fin m) ℝ) =
      rowsMatrix (gramSchmidtNormed ℝ (A t)) :=
  rfl

/-- Every matrix entry of the Gram--Schmidt `SO(m)` projection is jointly
smooth in the parameter.
@isnad1 id=contdiff.3h5v.s8.4ba8cca00654 from=translated src=- shape=cefdc512 vocab=59ad6da4
-/
theorem contDiff_gramSchmidtSO_apply
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {m : ℕ} (A : T → Fin m → EuclideanSpace ℝ (Fin m))
    (hA : ∀ i, ContDiff ℝ ∞ fun t => A t i)
    (hInd : ∀ t, LinearIndependent ℝ (A t))
    (hdet : ∀ t, 0 < (rowsMatrix (A t)).det) (i j : Fin m) :
    ContDiff ℝ ∞ fun t =>
      (((gramSchmidtSO A hInd hdet t : SOGroup m) :
        Matrix (Fin m) (Fin m) ℝ) i j) := by
  change ContDiff ℝ ∞ fun t =>
    WithLp.ofLp (gramSchmidtNormed ℝ (A t) i) j
  exact (EuclideanSpace.proj j).contDiff.comp
    (contDiff_gramSchmidtNormed_family hA hInd i)

/-! ## The positive-determinant matrix retraction -/

/-- Rowwise normalized Gram--Schmidt as a point of `SO(m)`, defined on every
matrix of positive determinant.-/
def matrixGramSchmidtSO {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (hdet : 0 < M.det) : SOGroup m :=
  ⟨rowsMatrix (gramSchmidtNormed ℝ (matrixRows M)),
    rowsMatrix_gramSchmidtNormed_mem_specialOrthogonalGroup
      (linearIndependent_matrixRows_of_det_ne_zero (ne_of_gt hdet))
      (by simpa using hdet)⟩

/--
@isnad1 id=eq.1h2v.s7.bdcb88eaf341 from=translated src=- shape=40698575 vocab=cc06f87c
-/
@[simp] theorem matrixGramSchmidtSO_coe {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (hdet : 0 < M.det) :
    ((matrixGramSchmidtSO M hdet : SOGroup m) :
      Matrix (Fin m) (Fin m) ℝ) =
      rowsMatrix (gramSchmidtNormed ℝ (matrixRows M)) :=
  rfl

/-- Each coordinate of the Gram--Schmidt projection is smooth for a smooth
family staying in the positive-determinant matrices.
@isnad1 id=contdiff.2h5v.s8.ed10e37fc73f from=translated src=- shape=24a10d11 vocab=1e596c62
-/
theorem contDiff_matrixGramSchmidtSO_apply
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {m : ℕ} (M : T → Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, ContDiff ℝ ∞ fun t => M t i j)
    (hdet : ∀ t, 0 < (M t).det) (i j : Fin m) :
    ContDiff ℝ ∞ fun t =>
      (((matrixGramSchmidtSO (M t) (hdet t) : SOGroup m) :
        Matrix (Fin m) (Fin m) ℝ) i j) := by
  change ContDiff ℝ ∞ fun t =>
    WithLp.ofLp (gramSchmidtNormed ℝ (matrixRows (M t)) i) j
  have hgs : ContDiff ℝ ∞ fun t =>
      gramSchmidtNormed ℝ (matrixRows (M t)) i := by
    apply contDiff_gramSchmidtNormed_family
    · exact contDiff_matrixRows hM
    · intro t
      exact linearIndependent_matrixRows_of_det_ne_zero
        (ne_of_gt (hdet t))
  change ContDiff ℝ ∞ ((EuclideanSpace.proj j) ∘ fun t =>
    gramSchmidtNormed ℝ (matrixRows (M t)) i)
  exact (EuclideanSpace.proj j).contDiff.comp hgs

/-- Every special-orthogonal matrix has positive determinant.
@isnad1 id=lt.0h2v.s8.0896b20a02c7 from=translated src=- shape=58b2323e vocab=45f00bd2
-/
theorem SOGroup_det_pos {m : ℕ} (Q : SOGroup m) :
    0 < ((Q : Matrix (Fin m) (Fin m) ℝ)).det := by
  rw [(Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).2]
  norm_num

/-- The positive-matrix Gram--Schmidt projection is a literal retraction on
`SO(m)`.  This exactness is what preserves relative collars after smooth
ambient-matrix approximation.
@isnad1 id=eq.0h2v.s8.7d8c3253c066 from=translated src=- shape=20c5b3a4 vocab=de07362b
-/
@[simp] theorem matrixGramSchmidtSO_of_SOGroup {m : ℕ} (Q : SOGroup m) :
    matrixGramSchmidtSO (Q : Matrix (Fin m) (Fin m) ℝ)
      (SOGroup_det_pos Q) = Q := by
  have horth : Orthonormal ℝ (matrixRows
      (Q : Matrix (Fin m) (Fin m) ℝ)) :=
    orthonormal_matrixRows_of_mem_orthogonalGroup
      (Matrix.mem_specialOrthogonalGroup_iff.mp Q.property).1
  apply Subtype.ext
  change rowsMatrix (gramSchmidtNormed ℝ
    (matrixRows (Q : Matrix (Fin m) (Fin m) ℝ))) =
      (Q : Matrix (Fin m) (Fin m) ℝ)
  rw [gramSchmidtNormed_eq_of_orthonormal horth,
    rowsMatrix_matrixRows]

end Submission
