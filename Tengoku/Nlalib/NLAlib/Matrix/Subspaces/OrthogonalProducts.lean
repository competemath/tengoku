import Tengoku.Nlalib.NLAlib.Matrix.Subspaces.Projections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Matrices with orthonormal columns: products, relabelling, rank and isometry

The generic API of `HasOrthonormalCols Q` (`Qᴴ Q = I`) beyond projectors and residuals
(`NLAlib.Matrix.Subspaces.Projections`), over `[RCLike 𝕜]`:

* closure: products (`HasOrthonormalCols.mul`), adjoints of square frames
  (`HasOrthonormalCols.conjTranspose`, `HasOrthonormalCols.mul_conjTranspose_self`), column
  selections (`HasOrthonormalCols.submatrix_cols`) and relabelling of rows and columns
  (`HasOrthonormalCols.reindex`);
* left multiplication by a frame preserves rank (`rank_isometry_mul_eq`);
* the induced Euclidean linear isometry (`HasOrthonormalCols.toLinearIsometry`);
* column identities: `(Qᴴ Q)ᵢⱼ = ⟨qᵢ, qⱼ⟩`, `Q v = ∑ⱼ vⱼ qⱼ`, orthonormality and linear
  independence of the columns, and the Euclidean inner product as a dot product
  (`inner_eq_star_dotProduct_ofLp`).

Horn–Johnson 2013, §2.1 and §0.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A product of column isometries is a column isometry. Horn–Johnson 2013, §2.1.
@isnad1 id=hasortho.2h6v.s6.3e90be1c645d from=translated src=- shape=3a7fe432 vocab=c0034ae8
-/
theorem HasOrthonormalCols.mul {m n p : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] [DecidableEq p] {P : Matrix m n 𝕜} {Q : Matrix n p 𝕜}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) : HasOrthonormalCols (P * Q) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P Q,
    hP.conjTranspose_mul_self, Matrix.one_mul, hQ.conjTranspose_mul_self]

/-- The row Gram matrix of a column isometry is an idempotent. Its Hermitian
property is the native row-Gram identity, so it is an orthogonal projector.
@isnad1 id=isidempo.1h4v.s7.59b4e5e9c15a from=translated src=- shape=be2653d8 vocab=2c10ffd9
-/
theorem HasOrthonormalCols.isIdempotentElem_mul_conjTranspose {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq n] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) : IsIdempotentElem (Q * Qᴴ) := by
  change (Q * Qᴴ) * (Q * Qᴴ) = Q * Qᴴ
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ Q Qᴴ, hQ.conjTranspose_mul_self,
    Matrix.one_mul]

/-- A square matrix with orthonormal columns is unitary: `U Uᴴ = I`. Horn–Johnson 2013, §2.1.
@isnad1 id=eq.1h3v.s7.21e14c8db21e from=translated src=- shape=fc2ace93 vocab=1105a194
-/
theorem HasOrthonormalCols.mul_conjTranspose_self {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : U * Uᴴ = 1 :=
  mul_eq_one_comm.mp hU.conjTranspose_mul_self

/-- The adjoint of a square unitary matrix is unitary, including empty matrices.
Horn–Johnson 2013, §2.1.
@isnad1 id=hasortho.1h3v.s6.cac4806a4e0d from=translated src=- shape=a58f3d99 vocab=c05e7e5b
-/
theorem HasOrthonormalCols.conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : HasOrthonormalCols Uᴴ := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
  exact hU.mul_conjTranspose_self

/-- A square matrix with orthonormal columns is invertible, with inverse `Uᴴ`.
Horn–Johnson 2013, §2.1.
@isnad1 id=isunit.1h3v.s5.8077e133ecfc from=translated src=- shape=70f196c8 vocab=c65ee332
-/
theorem HasOrthonormalCols.isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : IsUnit U :=
  ⟨⟨U, Uᴴ, hU.mul_conjTranspose_self, hU.conjTranspose_mul_self⟩, rfl⟩

/-- The inverse of a square matrix with orthonormal columns is its adjoint.
Horn–Johnson 2013, §2.1.
@isnad1 id=eq.1h3v.s6.145ca20debca from=translated src=- shape=d3ef3b1e vocab=c5fb60b2
-/
theorem HasOrthonormalCols.inv_eq_conjTranspose {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U) : U⁻¹ = Uᴴ :=
  Matrix.inv_eq_left_inv hU.conjTranspose_mul_self

/-- Selecting distinct columns of an orthonormal frame preserves orthonormality.
Horn–Johnson 2013, §2.1.
@isnad1 id=hasortho.1h6v.s6.f1eb52b2cada from=translated src=- shape=12e6f981 vocab=bec7a876
-/
theorem HasOrthonormalCols.submatrix_cols {m n r : Type*} [Fintype m] [Fintype n]
    [Fintype r] [DecidableEq n] [DecidableEq r] {Q : Matrix m n 𝕜}
    (hQ : HasOrthonormalCols Q) (e : r ↪ n) : HasOrthonormalCols (Q.submatrix id e) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_submatrix]
  have h := Matrix.submatrix_mul_equiv Qᴴ Q e (Equiv.refl m) e
  simp only [Equiv.coe_refl] at h
  rw [h, hQ.conjTranspose_mul_self]
  ext i j
  simp [Matrix.one_apply, e.injective.eq_iff]

/-- Relabelling rows and columns preserves orthonormal columns, including empty index types.
Horn–Johnson 2013, §2.1.
@isnad1 id=hasortho.1h8v.s6.99c83bf3059c from=translated src=- shape=a2e47c90 vocab=3522a32c
-/
theorem HasOrthonormalCols.reindex {m n p q : Type*} [Fintype m] [Fintype p] [DecidableEq n]
    [DecidableEq q] {U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (em : m ≃ p) (en : n ≃ q) :
    HasOrthonormalCols (U.reindex em en) := by
  rw [HasOrthonormalCols]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hU.conjTranspose_mul_self, Matrix.submatrix_one_equiv]

/-- A block-diagonal matrix with orthonormal-column blocks has orthonormal columns.
Horn–Johnson 2013, §2.1.
@isnad1 id=hasortho.2h7v.s7.498ecd0e348c from=translated src=- shape=caff564d vocab=32530dfd
-/
theorem HasOrthonormalCols.fromBlocks_diagonal {p q r s : Type*} [Fintype p] [Fintype q]
    [Fintype r] [Fintype s] [DecidableEq q] [DecidableEq s]
    {A : Matrix p q 𝕜} {B : Matrix r s 𝕜} (hA : HasOrthonormalCols A)
    (hB : HasOrthonormalCols B) : HasOrthonormalCols (Matrix.fromBlocks A 0 0 B) := by
  rw [HasOrthonormalCols]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    hA.conjTranspose_mul_self, hB.conjTranspose_mul_self, Matrix.fromBlocks_one]

/-- The identity has orthonormal columns.
@isnad1 id=hasortho.0h2v.s6.57e8e7928a45 from=translated src=- shape=a3b4d2c8 vocab=023bc405
-/
theorem hasOrthonormalCols_one {n : Type*} [Fintype n] [DecidableEq n] :
    HasOrthonormalCols (1 : Matrix n n 𝕜) := by
  simp [HasOrthonormalCols]

/-- A column isometry preserves matrix rank, including rectangular and empty isometries.
Horn–Johnson 2013, §0.4.
@isnad1 id=eq.1h6v.s7.3514b432de91 from=translated src=- shape=1af04741 vocab=7238c31f
-/
theorem rank_isometry_mul_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq p]
    {Q : Matrix m p 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix p n 𝕜) :
    (Q * A).rank = A.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  have hBack : Qᴴ * (Q * A) = A := by
    rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul]
  calc
    A.rank = (Qᴴ * (Q * A)).rank := congrArg Matrix.rank hBack.symm
    _ ≤ (Q * A).rank := Matrix.rank_mul_le_right _ _

/-- An orthonormal frame has rank exactly its number of columns, including
the zero-width endpoint.
@isnad1 id=eq.1h4v.s5.e38388072995 from=translated src=- shape=ad7ef1be vocab=297735d7
-/
theorem HasOrthonormalCols.rank_eq_card {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Q.rank = Fintype.card n := by
  simpa only [Matrix.mul_one, Matrix.rank_one] using
    rank_isometry_mul_eq hQ (1 : Matrix n n 𝕜)

/-- A matrix with orthonormal columns defines a linear isometry of the corresponding Euclidean
spaces (the map `Matrix.toEuclideanLin Q`); for a square unitary matrix this is a unitary
Euclidean isometry. Horn–Johnson 2013, §2.1.-/
def HasOrthonormalCols.toLinearIsometry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    EuclideanSpace 𝕜 n →ₗᵢ[𝕜] EuclideanSpace 𝕜 m where
  toLinearMap := Q.toEuclideanLin
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 (Q *ᵥ x.ofLp) : EuclideanSpace 𝕜 m)‖ ^ 2 = ‖x‖ ^ 2
    rw [norm_toLp_sq_eq_re_star_dotProduct,
      star_mulVec_dotProduct_mulVec_self_of_hasOrthonormalCols hQ]
    have h := norm_toLp_sq_eq_re_star_dotProduct (𝕜 := 𝕜) x.ofLp
    simp only [WithLp.toLp_ofLp] at h
    exact h.symm

/-- The linear isometry associated with an orthonormal-column matrix has
exactly its Euclidean matrix linear map.
@isnad1 id=eq.1h4v.s12.d4455e0f614b from=translated src=- shape=3e936e18 vocab=ed0b4357
-/
@[simp] theorem HasOrthonormalCols.toLinearIsometry_toLinearMap
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    hQ.toLinearIsometry.toLinearMap = Q.toEuclideanLin := rfl

/-- Converting a Euclidean linear isometry to its matrix yields orthonormal
columns, the converse of `HasOrthonormalCols.toLinearIsometry`.
@isnad1 id=hasortho.0h4v.s12.ba65a690aec4 from=translated src=- shape=49d67def vocab=f424e380
-/
theorem hasOrthonormalCols_toEuclideanLin_symm_linearIsometry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (f : EuclideanSpace 𝕜 n →ₗᵢ[𝕜] EuclideanSpace 𝕜 m) :
    HasOrthonormalCols (Matrix.toEuclideanLin.symm f.toLinearMap) := by
  apply (hasOrthonormalCols_iff_orthonormal _).mpr
  have hcol : (fun j => (WithLp.toLp 2
      ((Matrix.toEuclideanLin.symm f.toLinearMap).col j) : EuclideanSpace 𝕜 m)) =
      f ∘ (EuclideanSpace.basisFun n 𝕜) := by
    funext j
    have h := congrArg (fun g => g (EuclideanSpace.basisFun n 𝕜 j))
      (Matrix.toEuclideanLin.apply_symm_apply f.toLinearMap)
    simpa only [Function.comp_def, Matrix.toLpLin_apply,
      EuclideanSpace.basisFun_apply, EuclideanSpace.single, PiLp.ofLp_single,
      Matrix.mulVec_single, MulOpposite.op_one, one_smul, LinearIsometry.coe_toLinearMap] using h
  rw [hcol]
  exact (EuclideanSpace.basisFun n 𝕜).orthonormal.comp_linearIsometry f

/-- Matrix reconstruction after passing to the associated Euclidean linear
isometry recovers the original orthonormal-column matrix.
@isnad1 id=eq.1h4v.s12.3321d749450f from=translated src=- shape=fff99b8e vocab=60a3145a
-/
@[simp] theorem HasOrthonormalCols.toEuclideanLin_symm_toLinearIsometry
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) :
    Matrix.toEuclideanLin.symm hQ.toLinearIsometry.toLinearMap = Q :=
  Matrix.toEuclideanLin.symm_apply_apply Q

/-! ### Columns of a frame -/

section Columns

variable {n : Type*} [Fintype n]

/-- `(Qᴴ Q)_ij = ⟨q_i, q_j⟩ = star q_i ⬝ q_j`. Helper for `arnoldi-def`.
@isnad1 id=eq.0h6v.s7.1c2071374247 from=translated src=- shape=03b34062 vocab=4e45e779
-/
theorem conjTranspose_mul_self_apply {k : Type*} (Q : Matrix n k 𝕜) (i j : k) :
    (Qᴴ * Q) i j = star (Q.col i) ⬝ᵥ Q.col j := by
  simp [Matrix.mul_apply, dotProduct, Matrix.col]

omit [Fintype n] in
/-- `Q v = ∑ⱼ vⱼ qⱼ`. Helper for `arnoldi-def`.
@isnad1 id=eq.0h5v.s6.354985ebd1a3 from=translated src=- shape=3b666328 vocab=d2735a9c
-/
theorem mulVec_eq_sum_smul_col {k : Type*} [Fintype k] (Q : Matrix n k 𝕜) (v : k → 𝕜) :
    Q *ᵥ v = ∑ j, v j • Q.col j := by
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.col, mul_comm]

/-- Columns of a matrix with orthonormal columns: `⟨q_i, q_j⟩ = δ_ij`.
@isnad1 id=eq.1h6v.s7.98af50f9248c from=translated src=- shape=17f4b841 vocab=30aba175
-/
theorem HasOrthonormalCols.star_col_dotProduct_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k 𝕜} (hQ : HasOrthonormalCols Q) (i j : k) :
    star (Q.col i) ⬝ᵥ Q.col j = if i = j then 1 else 0 := by
  rw [← conjTranspose_mul_self_apply, hQ.conjTranspose_mul_self, Matrix.one_apply]

/-- Orthonormal columns are linearly independent. Helper for `graded-krylov-basis-def`.
@isnad1 id=linearin.1h4v.s6.e7d3f5c48392 from=translated src=- shape=2a5e769e vocab=6d6ebf88
-/
theorem HasOrthonormalCols.linearIndependent_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k 𝕜} (hQ : HasOrthonormalCols Q) : LinearIndependent 𝕜 Q.col := by
  rw [← Matrix.mulVec_injective_iff]
  intro x y hxy
  have h := congrArg (fun v => Qᴴ *ᵥ v) hxy
  simpa only [Matrix.mulVec_mulVec, hQ.conjTranspose_mul_self, Matrix.one_mulVec] using h

/-- The Euclidean inner product is the (conjugate-linear in the first slot) dot product of the
coordinates: `⟨x, y⟩ = star x ⬝ y`. Helper for `arnoldi-def`.
@isnad1 id=eq.0h4v.s7.20e654bf977e from=translated src=- shape=30e2eb55 vocab=cdfa3849
-/
theorem inner_eq_star_dotProduct_ofLp (x y : EuclideanSpace 𝕜 n) :
    inner 𝕜 x y = star x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

end Columns

end NLAlib
