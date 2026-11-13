import Tengoku.Nlalib.NLAlib.Matrix.Structured.JacobiBorders
import Tengoku.Nlalib.NLAlib.Matrix.Structured.TridiagonalPowers
import Tengoku.Seed.Logic.Equiv.Fin.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Reindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # First-coordinate moments of actual Jacobi borders

The finite reindexing places the scalar Schur corner after the leading matrix. Changing
this corner preserves moments through `2q`; adding the last coupling to a `(q+1)`-block
preserves moments through `2q+1`. Both statements include the smallest dimensions.
-/

noncomputable section
open Matrix Finset
open scoped Matrix
open scoped MatrixOrder

namespace NLAlib

variable {q : ℕ}

/-- The actual symmetric scalar border, on contiguous zero-based finite indices.-/
def finSymmetricBorder (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (symmetricBorder J v d)

/--
@isnad1 id=eq.0h6v.s5.76e28196962e from=translated src=- shape=e5aacf34 vocab=c51bca6a
-/
@[simp] theorem finSymmetricBorder_castSucc_castSucc
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) (i j : Fin q) :
    finSymmetricBorder J v d i.castSucc j.castSucc = J i j := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

/--
@isnad1 id=eq.0h5v.s5.e549d7c0827a from=translated src=- shape=3458327b vocab=26991441
-/
@[simp] theorem finSymmetricBorder_castSucc_last
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) (i : Fin q) :
    finSymmetricBorder J v d i.castSucc (Fin.last q) = v i := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

/--
@isnad1 id=eq.0h5v.s5.f81fbac4531c from=translated src=- shape=7dc3d63e vocab=26991441
-/
@[simp] theorem finSymmetricBorder_last_castSucc
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) (i : Fin q) :
    finSymmetricBorder J v d (Fin.last q) i.castSucc = v i := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

/--
@isnad1 id=eq.0h4v.s4.dac741309709 from=translated src=- shape=5c332878 vocab=7128a1a6
-/
@[simp] theorem finSymmetricBorder_last_last
    (J : Matrix (Fin q) (Fin q) ℝ) (v : Fin q → ℝ) (d : ℝ) :
    finSymmetricBorder J v d (Fin.last q) (Fin.last q) = d := by
  simp [finSymmetricBorder, symmetricBorder, Matrix.reindex]

/-- A border whose cross vector is supported at the last leading coordinate is
tridiagonal whenever its leading matrix is tridiagonal.
@isnad1 id=istridia.2h4v.s6.5dadccdfa363 from=translated src=- shape=cefc4067 vocab=fd449f32
-/
theorem isTridiagonal_finSymmetricBorder {J : Matrix (Fin q) (Fin q) ℝ}
    (hJ : IsTridiagonal J) {v : Fin q → ℝ} (hv : ∀ i, i.val + 1 < q → v i = 0)
    (d : ℝ) : IsTridiagonal (finSymmetricBorder J v d) := by
  constructor
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; simp only [Fin.val_last] at hij; omega
    · intro hij
      simpa using hv j (by simpa using hij)
    · intro hij
      simp only [Fin.val_last, Fin.val_castSucc] at hij
      have := i.isLt
      omega
    · intro hij
      simpa using hJ.1 i j (by simpa using hij)
  · intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · intro hij; simp only [Fin.val_last] at hij; omega
    · intro hij
      simpa only [transpose_apply, finSymmetricBorder_castSucc_last] using hv j (by simpa using hij)
    · intro hij
      simp only [Fin.val_last, Fin.val_castSucc] at hij
      have := i.isLt
      omega
    · intro hij
      simpa only [transpose_apply, finSymmetricBorder_castSucc_castSucc] using hJ.2 i j (by simpa using hij)

/-- Changing only the last corner of an actual `(q+1)`-dimensional tridiagonal border
preserves its rooted moments through degree `2q`.
Source: focused mathematical reroutes, Section 3, equations (BL1), (BL5).
atlas: gauss-radau-lobatto (partial)
@isnad1 id=eq.3h6v.s9.98757b6a7a3f from=translated src=- shape=b72c545f vocab=f517f221
-/
theorem pow_finSymmetricBorder_apply_zero_eq_of_corner
    {J : Matrix (Fin q) (Fin q) ℝ} (hJ : IsTridiagonal J)
    {v : Fin q → ℝ} (hv : ∀ i, i.val + 1 < q → v i = 0)
    (d c : ℝ) (k : ℕ) (hk : k ≤ 2 * q) :
    (finSymmetricBorder J v d ^ k) 0 0 = (finSymmetricBorder J v c ^ k) 0 0 := by
  apply pow_apply_zero_eq_of_isTridiagonal_of_eq_below_add
    (isTridiagonal_finSymmetricBorder hJ hv d) (isTridiagonal_finSymmetricBorder hJ hv c)
    (Nat.succ_pos q) (2 * q) _ k hk
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij; simp only [Fin.val_last] at hij; omega
  · intro _; simp
  · intro _; simp
  · intro _; simp

/-- Adding the last neighboring coupling to a `(q+1)`-dimensional block preserves
its rooted moments through degree `2q+1`, independently of the new corner.
Source: focused mathematical reroutes, Section 3, equations (BL1), (BL10).
atlas: gauss-radau-lobatto (partial)
@isnad1 id=eq.3h5v.s10.faeb94a8a7ef from=translated src=- shape=0df8d79d vocab=f517f221
-/
theorem pow_finSymmetricBorder_apply_zero_eq_of_coupling
    {J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ} (hJ : IsTridiagonal J)
    {v : Fin (q + 1) → ℝ} (hv : ∀ i, i.val < q → v i = 0)
    (d : ℝ) (k : ℕ) (hk : k ≤ 2 * q + 1) :
    (finSymmetricBorder J v d ^ k) 0 0 = (finSymmetricBorder J 0 d ^ k) 0 0 := by
  have hv' : ∀ i, i.val + 1 < q + 1 → v i = 0 := fun i hi => hv i (by omega)
  apply pow_apply_zero_eq_of_isTridiagonal_of_eq_below_add
    (isTridiagonal_finSymmetricBorder hJ hv' d)
    (isTridiagonal_finSymmetricBorder hJ (by simp) d)
    (by omega : 0 < (q + 1) + 1) (2 * q + 1) _ k hk
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij; simp only [Fin.val_last] at hij; omega
  · intro hij
    simpa using hv j (by simp only [Fin.val_last, Fin.val_castSucc] at hij; omega)
  · intro hij
    simpa using hv i (by simp only [Fin.val_last, Fin.val_castSucc] at hij; omega)
  · intro _; simp

/-- With no cross coupling, the rooted moments of the actual scalar border are those
of its leading block.
@isnad1 id=eq.0h4v.s9.22b8f98a4842 from=translated src=- shape=32c34721 vocab=6f233474
-/
theorem pow_finSymmetricBorder_zero_apply_zero
    (J : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ) (d : ℝ) (k : ℕ) :
    (finSymmetricBorder J 0 d ^ k) 0 0 = (J ^ k) 0 0 := by
  have hpow := (Matrix.reindexRingEquiv ℝ finSumFinEquiv).map_pow
    (symmetricBorder J 0 d) k
  change reindex finSumFinEquiv finSumFinEquiv (symmetricBorder J 0 d ^ k) =
    finSymmetricBorder J 0 d ^ k at hpow
  rw [← hpow]
  have hblock : symmetricBorder J 0 d =
      fromBlocks J 0 0 (of (fun _ _ => d) : Matrix (Fin 1) (Fin 1) ℝ) := rfl
  rw [hblock, fromBlocks_diagonal_pow]
  change (fromBlocks (J ^ k) 0 0 ((of (fun _ _ => d) : Matrix (Fin 1) (Fin 1) ℝ) ^ k))
    (Sum.inl (0 : Fin (q + 1))) (Sum.inl 0) = _
  rfl

/-- The finite indexed actual border inherits Hermitian symmetry from its leading
block, by the explicit reindexing.
@isnad1 id=ishermit.1h4v.s6.6f83e9cad928 from=translated src=- shape=cb7e5189 vocab=f809dcb5
-/
theorem isHermitian_finSymmetricBorder {J : Matrix (Fin q) (Fin q) ℝ}
    (hJ : J.IsHermitian) (v : Fin q → ℝ) (d : ℝ) :
    (finSymmetricBorder J v d).IsHermitian :=
  (isHermitian_symmetricBorder hJ v d).submatrix finSumFinEquiv.symm

/-- A last-coordinate border with a nonzero last coupling keeps every superdiagonal
nonzero when the leading superdiagonal is nonzero. The empty leading block is allowed.
@isnad1 id=ne.3h6v.s7.9ee943b98e1a from=translated src=- shape=ba579247 vocab=bdb9d963
-/
theorem finSymmetricBorder_superdiagonal_ne_zero
    {J : Matrix (Fin q) (Fin q) ℝ} {v : Fin q → ℝ} (d : ℝ)
    (hJ : ∀ i j : Fin q, i.val + 1 = j.val → J i j ≠ 0)
    (hv : ∀ i : Fin q, i.val + 1 = q → v i ≠ 0) :
    ∀ i j : Fin (q + 1), i.val + 1 = j.val → finSymmetricBorder J v d i j ≠ 0 := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hij; simp only [Fin.val_last] at hij; omega
  · intro hij
    simp only [Fin.val_last, Fin.val_castSucc] at hij
    have := j.isLt
    omega
  · intro hij
    simpa using hv i (by simpa using hij)
  · intro hij
    simpa using hJ i j (by simpa using hij)

/-- Relabelling finite coordinates preserves the positive-semidefinite matrix order.
@isnad1 id=le.1h5v.s7.5d0bdcdf7360 from=translated src=- shape=3f8f776b vocab=1ccb7b9b
-/
theorem reindex_le_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) {A B : Matrix ι ι ℝ} (h : A ≤ B) :
    reindex e e A ≤ reindex e e B := by
  rw [Matrix.le_iff] at h ⊢
  change ((B - A).submatrix e.symm e.symm).PosSemidef
  exact h.submatrix e.symm

/-- Scalar identity shifts commute with finite coordinate relabelling.
@isnad1 id=eq.0h4v.s7.ec468250e0e4 from=translated src=- shape=056933eb vocab=7a16c616
-/
theorem reindex_smul_one {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (a : ℝ) :
    reindex e e (a • (1 : Matrix ι ι ℝ)) = a • (1 : Matrix κ κ ℝ) := by
  ext i j
  simp [Matrix.reindex, Matrix.one_apply, e.symm.injective.eq_iff]

end NLAlib
