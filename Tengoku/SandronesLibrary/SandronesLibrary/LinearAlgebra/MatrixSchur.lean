/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.MatrixQR
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.JordanSimilarity
import Tengoku.SandronesLibrary.SandronesLibrary.LinearAlgebra.Eigenvalue
import Tengoku.Seed.Data.Fintype.Sort
import Tengoku.Seed.Order.Lattice
import Tengoku.Seed.Analysis.InnerProductSpace.ProdL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# LinearAlgebra / MatrixSchur —— Schur 分解

本文件证明任意复方阵都可由酉相似变换化为上三角矩阵。证明先把 Jordan 块按
词典序编号，得到保持上三角性的相似标准形；再对换基矩阵作复 QR 分解，把一般
相似变换改造成酉相似变换。

实 Schur 部分从复化矩阵的特征向量抽取一个至多二维的实不变子空间，随后在其正交补
上的压缩算子中递归。递归所得尾部正交基与首块正交基拼接后，给出对角块大小均为
`1×1` 或 `2×2` 的显式块上三角矩阵。

> **Entry**: linear-algebra.decomposition.schur
-/

namespace SandronesLibrary.LinearAlgebra.MatrixDecomposition

open Matrix
open SandronesLibrary.LinearAlgebra.OrthogonalUnitary
open SandronesLibrary.LinearAlgebra.Jordan

/-- 复 Schur 分解证书。-/
structure ComplexSchurFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) where
  unitary : Matrix (Fin n) (Fin n) ℂ
  upper : Matrix (Fin n) (Fin n) ℂ
  unitary_matrix : IsUnitaryMatrix unitary
  upper_triangular : upper.IsUpperTriangular
  eq_mul_conjTranspose : A = unitary * upper * unitaryᴴ

/-- 复矩阵的方 QR 分解。-/
structure ComplexQRFactorization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) where
  unitary : Matrix (Fin n) (Fin n) ℂ
  upper : Matrix (Fin n) (Fin n) ℂ
  unitary_matrix : IsUnitaryMatrix unitary
  upper_triangular : upper.IsUpperTriangular
  eq_mul : A = unitary * upper

noncomputable def complexQRColumns {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Fin n → EuclideanSpace ℂ (Fin n) :=
  fun j => WithLp.toLp 2 (Aᵀ j)

noncomputable def complexQRBasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
  InnerProductSpace.gramSchmidtOrthonormalBasis finrank_euclideanSpace
    (complexQRColumns A)

noncomputable def complexQRQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix (complexQRBasis A).toBasis

noncomputable def complexQRR {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (complexQRBasis A).toBasis.toMatrix (complexQRColumns A)

/-- 任意复方阵存在 QR 分解。
@isnad1 id=nonempty.0h2v.s3.bd03b9e63362 from=translated src=- shape=09bb2451 vocab=74589699
-/
theorem exists_complex_qr {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Nonempty (ComplexQRFactorization A) := by
  have hU : IsUnitaryMatrix (complexQRQ A) := by
    rw [complexQRQ, isUnitaryMatrix_iff_mem]
    exact (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary
      (complexQRBasis A)
  have hR : (complexQRR A).IsUpperTriangular := by
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular
      finrank_euclideanSpace (complexQRColumns A)
  have hmul : complexQRQ A * complexQRR A = A := by
    rw [complexQRQ, complexQRR, Module.Basis.toMatrix_mul_toMatrix]
    rfl
  exact ⟨{
    unitary := complexQRQ A
    upper := complexQRR A
    unitary_matrix := hU
    upper_triangular := hR
    eq_mul := hmul.symm }⟩

/-- 任意复方阵都相似于一个上三角矩阵。
@isnad1 id=isuppert.0h1v.s6.69598f4982a9 from=translated src=- shape=86d27193 vocab=ed40b1b3
-/
theorem jordanNormalMatrix_upper (d : JordanFormData ℂ)
    [LinearOrder d.Block] [DecidableEq d.Block] :
    (jordanNormalMatrix d).IsUpperTriangular := by
  letI := d.blockFintype
  intro p q hpq
  rcases p with ⟨i, k⟩
  rcases q with ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    have hlk : l < k := by simpa using hpq
    have hsucc : k.val + 1 ≠ l.val := by omega
    simp [jordanNormalMatrix, Matrix.blockDiagonal'_apply, jordanBlock,
      ne_of_gt hlk, hsucc]
  · simp [jordanNormalMatrix, Matrix.blockDiagonal'_apply, hij]

/--
@isnad1 id=isuppert.0h1v.s9.79fb48955147 from=translated src=- shape=9ee11873 vocab=d4db2ed1
-/
theorem jordanNormalMatrix_lex_upper (d : JordanFormData ℂ)
    [LinearOrder d.Block] [DecidableEq d.Block] :
    (Matrix.reindex
      (toLex : (Σ i : d.Block, Fin (d.length i + 1)) ≃
        Lex (Σ i : d.Block, Fin (d.length i + 1)))
      (toLex : (Σ i : d.Block, Fin (d.length i + 1)) ≃
        Lex (Σ i : d.Block, Fin (d.length i + 1)))
      (jordanNormalMatrix d)).IsUpperTriangular := by
  letI := d.blockFintype
  intro p q hpq
  rw [Matrix.reindex_apply]
  change (jordanNormalMatrix d) (ofLex p) (ofLex q) = 0
  change Sigma.Lex (· < ·) (fun _ => (· < ·))
      (ofLex q) (ofLex p) at hpq
  rcases hpq with @⟨i, j, a, b, hblock⟩ | @⟨i, a, b, hfiber⟩
  · have hne : j ≠ i := ne_of_gt hblock
    change (jordanNormalMatrix d) ⟨j, b⟩ ⟨i, a⟩ = 0
    simp [jordanNormalMatrix, Matrix.blockDiagonal'_apply, hne]
  · exact jordanNormalMatrix_upper d (Sigma.LT.fiber _ _ _ hfiber)

/--
@isnad1 id=eq.2h7v.s7.01031971b9a7 from=translated src=- shape=d954c57a vocab=5349a4b3
-/
theorem operatorMatrix_reindex_basis_schur
    {K V ι κ : Type*} [Field K] [AddCommGroup V]
    [SandronesLibrary.LinearAlgebra.VectorSpace.LinearSpace K V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (b : ι → V)
    (hb : SandronesLibrary.LinearAlgebra.VectorSpace.IsBasis K b)
    (hb' : SandronesLibrary.LinearAlgebra.VectorSpace.IsBasis K
      (fun k => b (e.symm k))) (T : V →ₗ[K] V) :
    SandronesLibrary.LinearAlgebra.Coordinates.operatorMatrix
        (fun k => b (e.symm k)) hb' T =
      Matrix.reindex e e
        (SandronesLibrary.LinearAlgebra.Coordinates.operatorMatrix b hb T) := by
  classical
  let B : Module.Basis ι K V := Module.Basis.mk hb.1 (by simpa [hb.2])
  let B' : Module.Basis κ K V := B.reindex e
  have hB (i : ι) : B i = b i := by simp [B]
  have hB' (k : κ) : B' k = b (e.symm k) := by simp [B', hB]
  change LinearMap.toMatrix
      (Module.Basis.mk hb'.1 (by simpa [hb'.2]))
      (Module.Basis.mk hb'.1 (by simpa [hb'.2])) T =
    Matrix.reindex e e
      (LinearMap.toMatrix (Module.Basis.mk hb.1 (by simpa [hb.2]))
        (Module.Basis.mk hb.1 (by simpa [hb.2])) T)
  have hmk : Module.Basis.mk hb.1 (by simpa [hb.2]) = B := by
    ext i
    simp [B]
  have hmk' : Module.Basis.mk hb'.1 (by simpa [hb'.2]) = B' := by
    ext k
    simp [hB']
  rw [hmk, hmk']
  ext i j
  simp [LinearMap.toMatrix_apply, B', Matrix.reindex_apply]

/--
@isnad1 id=ex.0h2v.s8.38a08fb1f484 from=translated src=- shape=2a0193ac vocab=f9243f98
-/
theorem exists_ordered_jordan_similar {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (B P Q : Matrix (Fin n) (Fin n) ℂ),
      B.IsUpperTriangular ∧ P * Q = 1 ∧ Q * P = 1 ∧ B = P * A * Q := by
  classical
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' A
  letI : IsAlgClosed ℂ :=
    SandronesLibrary.Analysis.Complex.complex_is_algebraically_closed
  obtain ⟨d, hd⟩ := exists_jordan_normal_basis T
  letI := d.blockFintype
  letI : LinearOrder d.Block := (Fintype.equivFin d.Block).linearOrder
  let I := Σ i : d.Block, Fin (d.length i + 1)
  dsimp [HasJordanNormalBasis] at hd
  change ∃ (b : I → (Fin n → ℂ))
    (hb : SandronesLibrary.LinearAlgebra.VectorSpace.IsBasis ℂ b),
      SandronesLibrary.LinearAlgebra.Coordinates.operatorMatrix b hb T =
        jordanNormalMatrix d at hd
  obtain ⟨b, hb, hmatrix⟩ := hd
  let BasisI : Module.Basis I ℂ (Fin n → ℂ) :=
    Module.Basis.mk hb.1 (by simpa [hb.2])
  have hcard : Fintype.card I = n := by
    have h := Module.finrank_eq_card_basis BasisI
    simpa [I] using h.symm
  let ILex := Lex I
  let toLexI : I ≃ ILex := toLex
  letI : Fintype ILex := Fintype.ofEquiv I toLexI
  have hcardLex : Fintype.card ILex = n := by
    rw [Fintype.card_congr toLexI.symm, hcard]
  let eo : ILex ≃o Fin n := (Fintype.orderIsoFinOfCardEq ILex hcardLex).symm
  let e : I ≃ Fin n := toLexI.trans eo.toEquiv
  let b' : Fin n → (Fin n → ℂ) := fun i => b (e.symm i)
  let B' : Module.Basis (Fin n) ℂ (Fin n → ℂ) := BasisI.reindex e
  have hB' (i : Fin n) : B' i = b' i := by simp [B', BasisI, b', e]
  have hB'fun : (B' : Fin n → (Fin n → ℂ)) = b' := funext hB'
  have hb' : SandronesLibrary.LinearAlgebra.VectorSpace.IsBasis ℂ b' := by
    refine ⟨?_, ?_⟩
    · rw [← hB'fun]
      exact B'.linearIndependent
    · rw [← hB'fun]
      simpa using B'.span_eq
  let J := Matrix.reindex e e (jordanNormalMatrix d)
  have hJ : SandronesLibrary.LinearAlgebra.Coordinates.operatorMatrix b' hb' T = J := by
    rw [operatorMatrix_reindex_basis_schur e b hb hb' T, hmatrix]
  have hJup : J.IsUpperTriangular := by
    intro i j hij
    dsimp only [J]
    rw [show Matrix.reindex e e (jordanNormalMatrix d) =
        Matrix.reindex eo.toEquiv eo.toEquiv
          (Matrix.reindex toLexI toLexI
            (jordanNormalMatrix d)) by
      ext p q
      rfl]
    rw [Matrix.reindex_apply]
    apply jordanNormalMatrix_lex_upper d
    exact eo.symm.lt_iff_lt.mpr hij
  let std : Fin n → (Fin n → ℂ) := fun i => Pi.single i 1
  have hstd : SandronesLibrary.LinearAlgebra.VectorSpace.IsBasis ℂ std := by
    let Std := Pi.basisFun ℂ (Fin n)
    have hStd (i : Fin n) : Std i = std i := by
      ext j
      simp [Std, std, Pi.basisFun_apply]
    have hStdFun : (Std : Fin n → (Fin n → ℂ)) = std := funext hStd
    refine ⟨?_, ?_⟩
    · rw [← hStdFun]
      exact Std.linearIndependent
    · rw [← hStdFun]
      simpa using Std.span_eq
  have hstandard :
      SandronesLibrary.LinearAlgebra.Coordinates.operatorMatrix std hstd T = A := by
    change LinearMap.toMatrix (Module.Basis.mk hstd.1 (by simpa [hstd.2]))
      (Module.Basis.mk hstd.1 (by simpa [hstd.2])) T = A
    have heq : Module.Basis.mk hstd.1 (by simpa [hstd.2]) =
        Pi.basisFun ℂ (Fin n) := by
      ext i j
      simp [std, Pi.basisFun_apply]
    rw [heq, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' A
  let P := SandronesLibrary.LinearAlgebra.Coordinates.transitionMatrix std b' hstd hb'
  let Q := SandronesLibrary.LinearAlgebra.Coordinates.transitionMatrix b' std hb' hstd
  refine ⟨J, P, Q, hJup, ?_, ?_, ?_⟩
  · exact SandronesLibrary.LinearAlgebra.Coordinates.transitionMatrix_mul_reverse
      std b' hstd hb'
  · exact SandronesLibrary.LinearAlgebra.Coordinates.reverse_mul_transitionMatrix
      std b' hstd hb'
  · rw [← hJ, SandronesLibrary.LinearAlgebra.Coordinates.operatorMatrix_change_basis
      std b' hstd hb' T, hstandard]

/--
@isnad1 id=ex.0h2v.s8.38a08fb1f484 from=translated src=- shape=2a0193ac vocab=f9243f98
-/
theorem exists_upper_similar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (B P Q : Matrix (Fin n) (Fin n) ℂ),
      B.IsUpperTriangular ∧ P * Q = 1 ∧ Q * P = 1 ∧ B = P * A * Q := by
  exact exists_ordered_jordan_similar A

/-- 复数域版本的“乘积反推左因子上三角”。
@isnad1 id=eq.2h5v.s6.fc93759fbe0c from=translated src=- shape=d56a377d vocab=0ab51666
-/
theorem complex_mul_apply_of_upper_of_left_prefix_zero {n : ℕ}
    (S R : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    (hR : R.IsUpperTriangular) (hprev : ∀ k, k < j → S i k = 0) :
    (S * R) i j = S i j * R j j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single j
  · intro k _ hkj
    rcases lt_trichotomy k j with hlt | heq | hgt
    · rw [hprev k hlt, zero_mul]
    · exact (hkj heq).elim
    · have hz : R k j = 0 := by
        apply hR
        change j < k
        exact hgt
      rw [hz, mul_zero]
  · simp

/--
@isnad1 id=isuppert.4h4v.s6.5918c24a0365 from=translated src=- shape=c6e99803 vocab=f9243f98
-/
theorem complex_upper_left_factor_of_mul {n : ℕ}
    (S R₁ R₂ : Matrix (Fin n) (Fin n) ℂ)
    (hR₁ : R₁.IsUpperTriangular) (hR₂ : R₂.IsUpperTriangular)
    (hdR₂ : ∀ i, R₂ i i ≠ 0) (hmul : S * R₂ = R₁) :
    S.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  revert hij
  apply wellFounded_lt.induction j
  intro j ih hij
  have hprev : ∀ k, k < j → S i k = 0 := by
    intro k hkj
    exact ih k hkj (hkj.trans hij)
  have heq : S i j * R₂ j j = 0 := by
    rw [← complex_mul_apply_of_upper_of_left_prefix_zero S R₂ i j hR₂ hprev]
    rw [hmul]
    apply hR₁
    change j < i
    exact hij
  exact (mul_eq_zero.mp heq).resolve_right (hdR₂ j)

/-- 任意复方阵存在酉 Schur 分解。
@isnad1 id=nonempty.0h2v.s3.c448a7bab25c from=translated src=- shape=09bb2451 vocab=156eb426
-/
theorem exists_complex_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Nonempty (ComplexSchurFactorization A) := by
  obtain ⟨B, P, Q, hBup, hPQ, hQP, hB⟩ := exists_upper_similar A
  let fac := Classical.choice (exists_complex_qr Q)
  let U := fac.unitary
  let R := fac.upper
  have hQ : Q = U * R := fac.eq_mul
  have hUleft : Uᴴ * U = 1 := fac.unitary_matrix
  have hUright : U * Uᴴ = 1 := by
    have hm := (isUnitaryMatrix_iff_mem U).mp fac.unitary_matrix
    exact Matrix.mem_unitaryGroup_iff.mp hm
  have hRP : R * P = Uᴴ := by
    calc
      R * P = 1 * (R * P) := (Matrix.one_mul _).symm
      _ = (Uᴴ * U) * (R * P) := by rw [hUleft]
      _ = Uᴴ * ((U * R) * P) := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * (Q * P) := by rw [← hQ]
      _ = Uᴴ := by rw [hQP, Matrix.mul_one]
  let T := Uᴴ * A * U
  have hTR : T * R = R * B := by
    calc
      T * R = Uᴴ * A * (U * R) := by simp only [T, Matrix.mul_assoc]
      _ = Uᴴ * A * Q := by rw [← hQ]
      _ = (R * P) * A * Q := by rw [hRP]
      _ = R * (P * A * Q) := by simp only [Matrix.mul_assoc]
      _ = R * B := by rw [hB]
  have hRBup : (R * B).IsUpperTriangular := fac.upper_triangular.mul hBup
  have hRdet : R.det ≠ 0 := by
    have hQdet : Q.det ≠ 0 := by
      intro hz
      have := congrArg Matrix.det hQP
      simp [Matrix.det_mul, hz] at this
    intro hRzero
    apply hQdet
    rw [hQ, Matrix.det_mul, hRzero, mul_zero]
  have hRdiag : ∀ i, R i i ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular fac.upper_triangular] at hRdet
    exact fun i => Finset.prod_ne_zero_iff.mp hRdet i (Finset.mem_univ i)
  have hTup : T.IsUpperTriangular :=
    complex_upper_left_factor_of_mul T (R * B) R hRBup fac.upper_triangular hRdiag hTR
  refine ⟨{
    unitary := U
    upper := T
    unitary_matrix := fac.unitary_matrix
    upper_triangular := hTup
    eq_mul_conjTranspose := ?_ }⟩
  calc
    A = 1 * A * 1 := by simp
    _ = (U * Uᴴ) * A * (U * Uᴴ) := by rw [hUright]
    _ = U * T * Uᴴ := by simp only [T, Matrix.mul_assoc]

/-- 复特征向量的实部、虚部张成一个至多二维的实不变子空间。
@isnad1 id=ex.0h2v.s9.9771cb130c7e from=translated src=- shape=47665109 vocab=3e7e55bf
-/
theorem exists_real_invariant_pair {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ (a b : ℝ) (x y : Fin (n + 1) → ℝ),
      (x ≠ 0 ∨ y ≠ 0) ∧
      A *ᵥ x = a • x - b • y ∧
      A *ᵥ y = b • x + a • y := by
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := A.map Complex.ofReal
  let T : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) := Matrix.toLin' C
  letI : IsAlgClosed ℂ :=
    SandronesLibrary.Analysis.Complex.complex_is_algebraically_closed
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨z, hzmem, hz0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Module.End.hasEigenvalue_iff.mp hμ)
  have hz : T z = μ • z := Module.End.mem_eigenspace_iff.mp hzmem
  let x : Fin (n + 1) → ℝ := fun i => (z i).re
  let y : Fin (n + 1) → ℝ := fun i => (z i).im
  refine ⟨μ.re, μ.im, x, y, ?_, ?_, ?_⟩
  · by_contra hxy
    push Not at hxy
    apply hz0
    funext i
    apply Complex.ext
    · exact congrFun hxy.1 i
    · exact congrFun hxy.2 i
  · funext i
    have hi := congrFun hz i
    have hre := congrArg Complex.re hi
    simpa [T, C, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, x, y, Complex.mul_re] using hre
  · funext i
    have hi := congrFun hz i
    have him := congrArg Complex.im hi
    simpa [T, C, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, x, y, Complex.mul_im, add_comm] using him

/-- 每个正维实方阵都有一个维数为一或二的非零不变子空间。-/
private theorem exists_real_invariant_subspace_finrank_le_two {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ∃ W : Submodule ℝ (Fin (n + 1) → ℝ),
      W ≠ ⊥ ∧ Module.finrank ℝ W ≤ 2 ∧
        ∀ v ∈ W, A *ᵥ v ∈ W := by
  obtain ⟨a, b, x, y, hxy, hx, hy⟩ := exists_real_invariant_pair A
  let s : Set (Fin (n + 1) → ℝ) := {x, y}
  let W : Submodule ℝ (Fin (n + 1) → ℝ) := Submodule.span ℝ s
  refine ⟨W, ?_, ?_, ?_⟩
  · intro hW
    rcases hxy with hx0 | hy0
    · apply hx0
      have hxm : x ∈ W := Submodule.mem_span_of_mem (by simp [s])
      rw [hW] at hxm
      simpa using hxm
    · apply hy0
      have hym : y ∈ W := Submodule.mem_span_of_mem (by simp [s])
      rw [hW] at hym
      simpa using hym
  · calc
      Module.finrank ℝ W ≤ s.toFinset.card := finrank_span_le_card s
      _ ≤ 2 := by
        have hcard : ({x, y} : Finset (Fin (n + 1) → ℝ)).card ≤ 2 := by
          calc
            _ ≤ ({y} : Finset (Fin (n + 1) → ℝ)).card + 1 := Finset.card_insert_le x {y}
            _ = 2 := by simp
        simpa only [s, Set.toFinset_insert, Set.toFinset_singleton] using hcard
  · let T : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) := Matrix.toLin' A
    have hmaps : W ≤ W.comap T := by
      change Submodule.span ℝ s ≤ W.comap T
      rw [Submodule.span_le]
      intro v hv
      simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with hv | hv
      · rw [hv]
        change A *ᵥ x ∈ W
        rw [hx]
        exact W.sub_mem (W.smul_mem a (Submodule.mem_span_of_mem (by simp [s])))
          (W.smul_mem b (Submodule.mem_span_of_mem (by simp [s])))
      · rw [hv]
        change A *ᵥ y ∈ W
        rw [hy]
        exact W.add_mem (W.smul_mem b (Submodule.mem_span_of_mem (by simp [s])))
          (W.smul_mem a (Submodule.mem_span_of_mem (by simp [s])))
    intro v hv
    simpa [T, Matrix.toLin'_apply', Matrix.mulVecLin_apply] using hmaps hv

/-- 由子空间及其正交补的标准正交基拼成全空间的适配正交归一基。-/
private noncomputable def adaptedOrthonormalBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ W) ⊕ Fin (Module.finrank ℝ Wᗮ))
      ℝ E :=
  ((stdOrthonormalBasis ℝ W).prod (stdOrthonormalBasis ℝ Wᗮ)).map
    W.orthogonalDecomposition.symm

/-- 算子在正交补上的压缩：先作用，再正交投影回 `Wᗮ`。-/
private noncomputable def orthogonalComplementCompression
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (W : Submodule ℝ E) :
    Wᗮ →ₗ[ℝ] Wᗮ :=
  Wᗮ.orthogonalProjectionOnto.toLinearMap.comp (T.comp Wᗮ.subtype)

universe u

/-- 实 Schur 分解的递归证书：每一步抽取维数一或二的不变子空间，
然后在其正交补压缩算子上继续。-/
private inductive RealSchurDecomposition :
    {E : Type u} → [NormedAddCommGroup E] → [InnerProductSpace ℝ E] →
      [FiniteDimensional ℝ E] → (E →ₗ[ℝ] E) → Type (u + 1)
  | zero {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E)
      (hzero : Module.finrank ℝ E = 0) : RealSchurDecomposition T
  | block {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (W : Submodule ℝ E)
      (nonzero : W ≠ ⊥)
      (finrank_le_two : Module.finrank ℝ W ≤ 2)
      (invariant : ∀ v ∈ W, T v ∈ W)
      (tail : RealSchurDecomposition (orthogonalComplementCompression T W)) :
      RealSchurDecomposition T

/-- 任意正维有限维实内积空间上的算子都有非零、至多二维的不变子空间。-/
private theorem exists_small_invariant_subspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E)
    (hpos : 0 < Module.finrank ℝ E) :
    ∃ W : Submodule ℝ E,
      W ≠ ⊥ ∧ Module.finrank ℝ W ≤ 2 ∧ ∀ v ∈ W, T v ∈ W := by
  classical
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let b₀ := stdOrthonormalBasis ℝ E
  let e : Fin (Module.finrank ℝ E) ≃ Fin (n + 1) := finCongr hn
  let b := b₀.reindex e
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    LinearMap.toMatrix b.toBasis b.toBasis T
  obtain ⟨Wc, hWc0, hWc2, hWcinv⟩ :=
    exists_real_invariant_subspace_finrank_le_two A
  let φ : E ≃ₗ[ℝ] (Fin (n + 1) → ℝ) := b.toBasis.equivFun
  let W : Submodule ℝ E := Wc.map φ.symm.toLinearMap
  refine ⟨W, ?_, ?_, ?_⟩
  · obtain ⟨z, hzWc, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWc0
    intro hW
    have hzW : φ.symm z ∈ W := by
      exact ⟨z, hzWc, rfl⟩
    rw [hW] at hzW
    apply hz0
    simpa using congrArg φ hzW
  · simpa only [W, LinearEquiv.finrank_map_eq] using hWc2
  · intro v hv
    rcases hv with ⟨z, hzWc, rfl⟩
    have hTz := hWcinv z hzWc
    refine ⟨φ (T (φ.symm z)), ?_, by simp⟩
    have hcoord : φ (T (φ.symm z)) = Matrix.mulVec A z := by
      have hm := LinearMap.toMatrix_mulVec_repr
        b.toBasis b.toBasis T (φ.symm z)
      have hzrepr : ⇑(b.toBasis.repr (φ.symm z)) = z := by
        ext i
        simp [φ]
      rw [hzrepr] at hm
      symm
      ext i
      simpa [φ, A] using congrFun hm i
    rw [hcoord]
    exact hTz

/-- 任意有限维实内积空间上的线性算子都有递归实 Schur 分解。-/
private theorem exists_realSchurDecomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) :
    Nonempty (RealSchurDecomposition T) := by
  by_cases hzero : Module.finrank ℝ E = 0
  · exact ⟨RealSchurDecomposition.zero T hzero⟩
  · have hpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hzero
    obtain ⟨W, hW0, hW2, hWinv⟩ := exists_small_invariant_subspace T hpos
    have hWpos : 0 < Module.finrank ℝ W := by
      exact Nat.pos_of_ne_zero ((Submodule.finrank_eq_zero.not).mpr hW0)
    have hdim : Module.finrank ℝ Wᗮ < Module.finrank ℝ E := by
      rw [← W.finrank_add_finrank_orthogonal]
      omega
    obtain ⟨tail⟩ := exists_realSchurDecomposition (orthogonalComplementCompression T W)
    exact ⟨RealSchurDecomposition.block T W hW0 hW2 hWinv tail⟩
termination_by Module.finrank ℝ E
decreasing_by exact hdim

/-- 递归块上三角矩阵：每个首块大小为一或二，左下块为零，右下块递归满足同一性质。-/
inductive IsRealSchurBlockUpper : {ι : Type} → [Fintype ι] → Matrix ι ι ℝ → Prop
  | empty {ι : Type} [Fintype ι] [IsEmpty ι] (A : Matrix ι ι ℝ) :
      IsRealSchurBlockUpper A
  | block {m n : Type} [Fintype m] [Fintype n]
      (A : Matrix (m ⊕ n) (m ⊕ n) ℝ)
      (head_size : Fintype.card m = 1 ∨ Fintype.card m = 2)
      (lower_left_zero : ∀ i j, A (Sum.inr i) (Sum.inl j) = 0)
      (tail : IsRealSchurBlockUpper (fun i j => A (Sum.inr i) (Sum.inr j))) :
      IsRealSchurBlockUpper A

/-- 一个算子的显式实 Schur 证书：某个正交基下的矩阵递归块上三角。-/
structure ExplicitRealSchur
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) where
  ι : Type
  [indexFintype : Fintype ι]
  [indexDecidableEq : DecidableEq ι]
  basis : OrthonormalBasis ι ℝ E
  blockUpper : IsRealSchurBlockUpper
    (LinearMap.toMatrix basis.toBasis basis.toBasis T)

/-- 把 `W` 的标准正交基和 `Wᗮ` 上任意正交基拼接成 `E` 的正交基。-/
private noncomputable def adaptedOrthonormalBasisWith
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E)
    {ι : Type} [Fintype ι] (c : OrthonormalBasis ι ℝ Wᗮ) :
    OrthonormalBasis (Fin (Module.finrank ℝ W) ⊕ ι) ℝ E :=
  ((stdOrthonormalBasis ℝ W).prod c).map W.orthogonalDecomposition.symm

/-- 广义适配基的左半部分属于 `W`。-/
private theorem adaptedOrthonormalBasisWith_inl_mem
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E)
    {ι : Type} [Fintype ι] (c : OrthonormalBasis ι ℝ Wᗮ)
    (i : Fin (Module.finrank ℝ W)) :
    adaptedOrthonormalBasisWith W c (Sum.inl i) ∈ W := by
  rw [adaptedOrthonormalBasisWith, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply, Submodule.orthogonalDecomposition_symm_apply]
  simpa using (stdOrthonormalBasis ℝ W i).property

/-- 广义适配基的右半部分就是给定的正交补基。-/
private theorem adaptedOrthonormalBasisWith_inr_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E)
    {ι : Type} [Fintype ι] (c : OrthonormalBasis ι ℝ Wᗮ) (i : ι) :
    adaptedOrthonormalBasisWith W c (Sum.inr i) = (c i : E) := by
  rw [adaptedOrthonormalBasisWith, OrthonormalBasis.map_apply,
    OrthonormalBasis.prod_apply, Submodule.orthogonalDecomposition_symm_apply]
  simp

/-- 不变子空间保证广义适配矩阵的左下块为零。-/
private theorem adaptedWith_operator_lowerLeft_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (W : Submodule ℝ E)
    (hW : ∀ v ∈ W, T v ∈ W)
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : OrthonormalBasis ι ℝ Wᗮ)
    (i : ι) (j : Fin (Module.finrank ℝ W)) :
    LinearMap.toMatrix (adaptedOrthonormalBasisWith W c).toBasis
      (adaptedOrthonormalBasisWith W c).toBasis T (Sum.inr i) (Sum.inl j) = 0 := by
  rw [LinearMap.toMatrix_apply]
  change ((adaptedOrthonormalBasisWith W c).repr
    (T (adaptedOrthonormalBasisWith W c (Sum.inl j)))).ofLp (Sum.inr i) = 0
  rw [OrthonormalBasis.repr_apply_apply, adaptedOrthonormalBasisWith_inr_apply]
  exact ((Submodule.mem_orthogonal' W _).mp (c i).property) _
    (hW _ (adaptedOrthonormalBasisWith_inl_mem W c j))

/-- 广义适配矩阵的右下块是压缩算子在给定尾部基下的矩阵。-/
private theorem orthogonalComplementCompression_matrix_with
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (W : Submodule ℝ E)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : OrthonormalBasis ι ℝ Wᗮ) (i j : ι) :
    LinearMap.toMatrix c.toBasis c.toBasis
        (orthogonalComplementCompression T W) i j =
      LinearMap.toMatrix (adaptedOrthonormalBasisWith W c).toBasis
        (adaptedOrthonormalBasisWith W c).toBasis T (Sum.inr i) (Sum.inr j) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  change (c.repr (orthogonalComplementCompression T W (c j))).ofLp i =
    ((adaptedOrthonormalBasisWith W c).repr
      (T (adaptedOrthonormalBasisWith W c (Sum.inr j)))).ofLp (Sum.inr i)
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    adaptedOrthonormalBasisWith_inr_apply, adaptedOrthonormalBasisWith_inr_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

/-- 递归实 Schur 证书可以展平为一个正交基及其显式块上三角矩阵。-/
private theorem RealSchurDecomposition.toExplicit
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}
    (d : RealSchurDecomposition T) : Nonempty (ExplicitRealSchur T) := by
  induction d with
  | @zero E _ _ _ T hzero =>
      let b := stdOrthonormalBasis ℝ E
      letI : IsEmpty (Fin (Module.finrank ℝ E)) := by
        rw [hzero]
        infer_instance
      exact ⟨{
        ι := Fin (Module.finrank ℝ E)
        basis := b
        blockUpper := IsRealSchurBlockUpper.empty _ }⟩
  | block T W hW0 hW2 hWinv tail ih =>
      obtain ⟨tailExplicit⟩ := ih
      letI := tailExplicit.indexFintype
      letI := tailExplicit.indexDecidableEq
      let b := adaptedOrthonormalBasisWith W tailExplicit.basis
      have hWpos : 0 < Module.finrank ℝ W :=
        Nat.pos_of_ne_zero ((Submodule.finrank_eq_zero.not).mpr hW0)
      have hsize : Fintype.card (Fin (Module.finrank ℝ W)) = 1 ∨
          Fintype.card (Fin (Module.finrank ℝ W)) = 2 := by
        simp only [Fintype.card_fin]
        omega
      exact ⟨{
        ι := Fin (Module.finrank ℝ W) ⊕ tailExplicit.ι
        basis := b
        blockUpper := IsRealSchurBlockUpper.block _ hsize
          (adaptedWith_operator_lowerLeft_zero T W hWinv tailExplicit.basis)
          (by
            rw [← funext₂ (orthogonalComplementCompression_matrix_with
              T W tailExplicit.basis)]
            exact tailExplicit.blockUpper) }⟩

/-- 任意有限维实内积空间上的算子都有显式实 Schur 块上三角化。
@isnad1 id=nonempty.0h2v.s6.72f1c1daf5df from=translated src=- shape=550f4138 vocab=4a5333dc
-/
theorem exists_explicitRealSchur
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) :
    Nonempty (ExplicitRealSchur T) := by
  obtain ⟨d⟩ := exists_realSchurDecomposition T
  exact d.toExplicit

end SandronesLibrary.LinearAlgebra.MatrixDecomposition
