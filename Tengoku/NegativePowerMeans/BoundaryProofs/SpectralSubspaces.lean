import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.Interlacing
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spectral-subspace machinery

Common finite-dimensional spectral-subspace and quadratic-form ingredients
used by the standalone proofs of multiplicative Lidskii and interlacing.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- The columns selected from a decreasingly ordered Hermitian eigenbasis.-/
noncomputable def spectralIsometry
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (e : Fin k ↪ Fin n) : Matrix (Fin n) (Fin k) 𝕜 :=
  fun p i ↦ decreasingEigenvectorUnitary hA p (e i)

/-- Selected columns of a unitary eigenvector matrix remain orthonormal.-/
theorem spectralIsometry_isometry
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (e : Fin k ↪ Fin n) : MatrixIsometry (spectralIsometry hA e) := by
  have hU := decreasingEigenvectorUnitary_isometry hA
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin n) (Fin n) 𝕜 ↦ M (e i) (e j)) hU
  simpa [MatrixIsometry, spectralIsometry, Matrix.mul_apply,
    Matrix.one_apply] using hij

/-- A selected spectral isometry intertwines the Hermitian matrix with the
diagonal matrix of its selected eigenvalues.-/
theorem mul_spectralIsometry
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (e : Fin k ↪ Fin n) :
    A * spectralIsometry hA e =
      spectralIsometry hA e * Matrix.diagonal
        (fun i ↦ RCLike.ofReal (decreasingEigenvalues hA (e i))) := by
  have hU := mul_decreasingEigenvectorUnitary hA
  ext p i
  have hi := congrArg
    (fun M : Matrix (Fin n) (Fin n) 𝕜 ↦ M p (e i)) hU
  rw [Matrix.mul_diagonal] at hi
  rw [Matrix.mul_diagonal]
  simpa [spectralIsometry, Matrix.mul_apply] using hi

/-- Compression to a selected spectral subspace is diagonal.-/
theorem compress_spectralIsometry
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (e : Fin k ↪ Fin n) :
    compress (spectralIsometry hA e) A =
      Matrix.diagonal
        (fun i ↦ RCLike.ofReal (decreasingEigenvalues hA (e i))) := by
  let V := spectralIsometry hA e
  let D : Matrix (Fin k) (Fin k) 𝕜 := Matrix.diagonal
    (fun i ↦ RCLike.ofReal (decreasingEigenvalues hA (e i)))
  have hV : MatrixIsometry V := spectralIsometry_isometry hA e
  have hrel : A * V = V * D := mul_spectralIsometry hA e
  calc
    compress V A = V.conjTranspose * (A * V) := by
      simp [compress, Matrix.mul_assoc]
    _ = V.conjTranspose * (V * D) := by rw [hrel]
    _ = (V.conjTranspose * V) * D := by rw [Matrix.mul_assoc]
    _ = D := by rw [hV, Matrix.one_mul]
    _ = Matrix.diagonal
        (fun i ↦ RCLike.ofReal (decreasingEigenvalues hA (e i))) := rfl

/-- The Euclidean linear map represented by an isometry matrix is injective.-/
theorem toEuclideanLin_injective_of_isometry
    {n k : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {V : Matrix (Fin n) (Fin k) 𝕜} (hV : MatrixIsometry V) :
    Function.Injective (Matrix.toEuclideanLin V) := by
  intro x y hxy
  apply WithLp.ofLp_injective 2
  apply hV.mulVec_injective
  have h := congrArg WithLp.ofLp hxy
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h

/-- The first `i + 1` coordinates, embedded into `Fin n`.-/
def topFinEmbeddingAt {n : ℕ} (i : Fin n) : Fin (i.val + 1) ↪ Fin n :=
  Fin.castLEEmb (Nat.succ_le_iff.mpr i.isLt)

/-- The last `n - i` coordinates, starting at coordinate `i`.-/
def bottomFinEmbeddingAt {n : ℕ} (i : Fin n) : Fin (n - i.val) ↪ Fin n :=
  bottomFinEmbedding (Nat.sub_le n i.val)

/-- The top spectral subspace of one Hermitian matrix and the bottom spectral
subspace of another, with complementary dimensions adding to `n + 1`, have a
nonzero common vector.-/
theorem spectral_subspaces_intersect
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin n) :
    ∃ (x : EuclideanSpace 𝕜 (Fin (i.val + 1)))
      (y : EuclideanSpace 𝕜 (Fin (n - i.val))),
        x ≠ 0 ∧ y ≠ 0 ∧
          Matrix.toEuclideanLin
              (spectralIsometry hA (topFinEmbeddingAt i)) x =
            Matrix.toEuclideanLin
              (spectralIsometry hB (bottomFinEmbeddingAt i)) y := by
  let VA := spectralIsometry hA (topFinEmbeddingAt i)
  let VB := spectralIsometry hB (bottomFinEmbeddingAt i)
  let LA := Matrix.toEuclideanLin VA
  let LB := Matrix.toEuclideanLin VB
  let F :
      (EuclideanSpace 𝕜 (Fin (i.val + 1)) ×
          EuclideanSpace 𝕜 (Fin (n - i.val))) →ₗ[𝕜]
        EuclideanSpace 𝕜 (Fin n) :=
    LA.comp (LinearMap.fst 𝕜 _ _) - LB.comp (LinearMap.snd 𝕜 _ _)
  have hrank : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) <
      Module.finrank 𝕜
        (EuclideanSpace 𝕜 (Fin (i.val + 1)) ×
          EuclideanSpace 𝕜 (Fin (n - i.val))) := by
    simp
    omega
  have hker : F.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hrank
  obtain ⟨z, hzmem, hz0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  rcases z with ⟨x, y⟩
  have hzero : F (x, y) = 0 := hzmem
  have heq : LA x = LB y := by
    have : LA x - LB y = 0 := by simpa [F] using hzero
    exact sub_eq_zero.mp this
  have hLA : Function.Injective LA := by
    exact toEuclideanLin_injective_of_isometry
      (spectralIsometry_isometry hA (topFinEmbeddingAt i))
  have hLB : Function.Injective LB := by
    exact toEuclideanLin_injective_of_isometry
      (spectralIsometry_isometry hB (bottomFinEmbeddingAt i))
  have hx0 : x ≠ 0 := by
    intro hx
    have hy : y = 0 := hLB (by simpa [hx] using heq.symm)
    exact hz0 (by simp [hx, hy])
  have hy0 : y ≠ 0 := by
    intro hy
    have hx : x = 0 := hLA (by simpa [hy] using heq)
    exact hz0 (by simp [hx, hy])
  exact ⟨x, y, hx0, hy0, by simpa [LA, LB, VA, VB] using heq⟩

/-- The real quadratic form associated with a matrix.-/
def realQuadraticForm
    {n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ A.mulVec x)

/-- Star converts a matrix-vector product into multiplication by the
conjugate transpose on the other side.-/
theorem star_mulVec
    {m n : Type*} [Fintype n] {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix m n 𝕜) (x : n → 𝕜) :
    star (A.mulVec x) = Matrix.vecMul (star x) A.conjTranspose := by
  funext i
  change star (∑ j, A i j * x j) = ∑ j, star (x j) * star (A i j)
  simp [mul_comm]

/-- Pulling a quadratic form back along a matrix is the same as applying the
quadratic form of the corresponding compression.-/
theorem realQuadraticForm_mulVec
    {m n : Type*} [Fintype m] [Fintype n]
    {𝕜 : Type*} [RCLike 𝕜]
    (V : Matrix m n 𝕜) (A : Matrix m m 𝕜) (x : n → 𝕜) :
    realQuadraticForm A (V.mulVec x) =
      realQuadraticForm (compress V A) x := by
  unfold realQuadraticForm compress
  congr 1
  rw [star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec]
  simp [Matrix.mul_assoc]

/-- A diagonal real matrix has the expected weighted-square quadratic form.-/
theorem realQuadraticForm_diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    {𝕜 : Type*} [RCLike 𝕜]
    (d : n → ℝ) (x : n → 𝕜) :
    realQuadraticForm
        (Matrix.diagonal (fun i ↦ RCLike.ofReal (d i))) x =
      ∑ i, d i * ‖x i‖ ^ 2 := by
  have hmul : (Matrix.diagonal
      (fun i ↦ RCLike.ofReal (d i))).mulVec x =
      fun i ↦ RCLike.ofReal (d i) * x i := by
    ext i
    simp [Matrix.mulVec]
  unfold realQuadraticForm
  rw [hmul]
  simp only [dotProduct]
  change RCLike.re (∑ i, star (x i) *
      (RCLike.ofReal (d i) * x i)) = _
  rw [show RCLike.re (∑ i, star (x i) *
      (RCLike.ofReal (d i) * x i)) =
      ∑ i, RCLike.re (star (x i) *
        (RCLike.ofReal (d i) * x i)) by
    exact map_sum RCLike.reLm _ Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.norm_sq_eq_def]
  simp [RCLike.mul_re, RCLike.star_def]
  ring

/-- Loewner order compares all real quadratic forms.-/
theorem realQuadraticForm_mono
    {n : Type*} [Fintype n]
    {𝕜 : Type*} [RCLike 𝕜]
    {A B : Matrix n n 𝕜} (hAB : A ≤ B) (x : n → 𝕜) :
    realQuadraticForm A x ≤ realQuadraticForm B x := by
  have hnonneg := (Matrix.le_iff.mp hAB).re_dotProduct_nonneg x
  unfold realQuadraticForm
  simpa [Matrix.sub_mulVec, dotProduct_sub] using hnonneg

/-- An isometry matrix preserves the Euclidean norm.-/
theorem norm_toEuclideanLin_of_isometry
    {m n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {V : Matrix (Fin m) (Fin n) 𝕜} (hV : MatrixIsometry V)
    (x : EuclideanSpace 𝕜 (Fin n)) :
    ‖Matrix.toEuclideanLin V x‖ = ‖x‖ := by
  have qform_one (r : ℕ) (z : EuclideanSpace 𝕜 (Fin r)) :
      realQuadraticForm (1 : Matrix (Fin r) (Fin r) 𝕜) z.ofLp = ‖z‖ ^ 2 := by
    unfold realQuadraticForm
    rw [Matrix.one_mulVec, dotProduct_comm,
      ← EuclideanSpace.inner_eq_star_dotProduct]
    exact inner_self_eq_norm_sq (𝕜 := 𝕜) z
  have hq := realQuadraticForm_mulVec V
    (1 : Matrix (Fin m) (Fin m) 𝕜) x.ofLp
  have hcomp : compress V (1 : Matrix (Fin m) (Fin m) 𝕜) = 1 := by
    simpa [compress, MatrixIsometry] using hV
  rw [hcomp] at hq
  have hout : realQuadraticForm (1 : Matrix (Fin m) (Fin m) 𝕜)
      (V.mulVec x.ofLp) = ‖Matrix.toEuclideanLin V x‖ ^ 2 := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
      qform_one m (Matrix.toEuclideanLin V x)
  have hin := qform_one n x
  rw [hout, hin] at hq
  nlinarith [norm_nonneg (Matrix.toEuclideanLin V x), norm_nonneg x]

/-- The quadratic form of the identity matrix is the sum of coordinate norm
squares.-/
theorem realQuadraticForm_one
    {n : Type*} [Fintype n] [DecidableEq n]
    {𝕜 : Type*} [RCLike 𝕜] (x : n → 𝕜) :
    realQuadraticForm (1 : Matrix n n 𝕜) x = ∑ i, ‖x i‖ ^ 2 := by
  have hone : (1 : Matrix n n 𝕜) =
      Matrix.diagonal (fun _ ↦ RCLike.ofReal 1) := by
    simp
  rw [hone, realQuadraticForm_diagonal]
  simp

/-- The quadratic form of a real scalar matrix is the corresponding scalar
multiple of the identity quadratic form.-/
theorem realQuadraticForm_scalar
    {n : Type*} [Fintype n] [DecidableEq n]
    {𝕜 : Type*} [RCLike 𝕜] (c : ℝ) (x : n → 𝕜) :
    realQuadraticForm (Matrix.scalar n (RCLike.ofReal c)) x =
      c * realQuadraticForm (1 : Matrix n n 𝕜) x := by
  rw [Matrix.scalar_apply, realQuadraticForm_diagonal,
    realQuadraticForm_one, Finset.mul_sum]

/-- On the span of the first `i + 1` eigenvectors, the quadratic form is
bounded below by the `i`th decreasing eigenvalue.-/
theorem top_spectral_quadratic_lower
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (i : Fin n) (x : EuclideanSpace 𝕜 (Fin (i.val + 1))) :
    decreasingEigenvalues hA i * ‖x‖ ^ 2 ≤
      realQuadraticForm A
        ((spectralIsometry hA (topFinEmbeddingAt i)).mulVec x.ofLp) := by
  let e := topFinEmbeddingAt i
  let V := spectralIsometry hA e
  calc
    decreasingEigenvalues hA i * ‖x‖ ^ 2 =
        ∑ j, decreasingEigenvalues hA i * ‖x.ofLp j‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    _ ≤ ∑ j, decreasingEigenvalues hA (e j) * ‖x.ofLp j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hji : e j ≤ i := by
        change j.val ≤ i.val
        omega
      exact mul_le_mul_of_nonneg_right
        (decreasingEigenvalues_antitone hA hji) (sq_nonneg _)
    _ = realQuadraticForm
        (Matrix.diagonal
          (fun j ↦ RCLike.ofReal (decreasingEigenvalues hA (e j))))
        x.ofLp := (realQuadraticForm_diagonal _ _).symm
    _ = realQuadraticForm (compress V A) x.ofLp := by
      rw [compress_spectralIsometry]
    _ = realQuadraticForm A (V.mulVec x.ofLp) :=
      (realQuadraticForm_mulVec V A x.ofLp).symm
    _ = realQuadraticForm A
        ((spectralIsometry hA (topFinEmbeddingAt i)).mulVec x.ofLp) := rfl

/-- On the span of the eigenvectors from `i` through the final coordinate,
the quadratic form is bounded above by the `i`th decreasing eigenvalue.-/
theorem bottom_spectral_quadratic_upper
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (i : Fin n) (x : EuclideanSpace 𝕜 (Fin (n - i.val))) :
    realQuadraticForm A
        ((spectralIsometry hA (bottomFinEmbeddingAt i)).mulVec x.ofLp) ≤
      decreasingEigenvalues hA i * ‖x‖ ^ 2 := by
  let e := bottomFinEmbeddingAt i
  let V := spectralIsometry hA e
  calc
    realQuadraticForm A (V.mulVec x.ofLp) =
        realQuadraticForm (compress V A) x.ofLp :=
      realQuadraticForm_mulVec V A x.ofLp
    _ = realQuadraticForm
        (Matrix.diagonal
          (fun j ↦ RCLike.ofReal (decreasingEigenvalues hA (e j))))
        x.ofLp := by
      rw [compress_spectralIsometry]
    _ = ∑ j, decreasingEigenvalues hA (e j) * ‖x.ofLp j‖ ^ 2 :=
      realQuadraticForm_diagonal _ _
    _ ≤ ∑ j, decreasingEigenvalues hA i * ‖x.ofLp j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hij : i ≤ e j := by
        change i.val ≤ n - (n - i.val) + j.val
        omega
      exact mul_le_mul_of_nonneg_right
        (decreasingEigenvalues_antitone hA hij) (sq_nonneg _)
    _ = decreasingEigenvalues hA i * ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]

end HiaiLimPowerMeans
