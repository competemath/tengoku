module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Homogeneous
public import Tengoku.Seed.LinearAlgebra.Matrix.Adjugate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section
namespace ChoppedPlane
open Matrix MvPolynomial

variable {R : Type*} [CommRing R] {c : ℕ}

/-- The maximal minor obtained by deleting row `i`.-/
def maximalMinor (B : Matrix (Fin (c + 1)) (Fin c) R) (i : Fin (c + 1)) : R :=
  (B.submatrix i.succAbove id).det

/-- The alternating cofactor row in the Hilbert–Burch complex.-/
def signedMaximalMinor (B : Matrix (Fin (c + 1)) (Fin c) R) (i : Fin (c + 1)) : R :=
  (-1) ^ i.val * maximalMinor B i

/-- Determinantal cofactors annihilate every column of the matrix.
@isnad1 id=eq.0h4v.s7.d443f6095d4e from=translated src=- shape=03800356 vocab=49f2f49b
-/
theorem signedMaximalMinor_relation (B : Matrix (Fin (c + 1)) (Fin c) R) (j : Fin c) :
    ∑ i, signedMaximalMinor B i * B i j = 0 := by
  classical
  let M : Matrix (Fin (c + 1)) (Fin (c + 1)) R :=
    fun i k => Fin.cases (B i j) (B i) k
  have hzero : M.det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := 0) (j := j.succ)
    · exact (Fin.succ_ne_zero j).symm
    · intro i
      simp [M]
  rw [Matrix.det_succ_column_zero] at hzero
  have hm (i : Fin (c + 1)) : M.submatrix i.succAbove Fin.succ = B.submatrix i.succAbove id := by
    ext k l
    change Fin.cases (B (i.succAbove k) j) (B (i.succAbove k)) l.succ = B (i.succAbove k) l
    exact Fin.cases_succ l
  simpa [signedMaximalMinor, maximalMinor, hm, M, mul_assoc, mul_comm, mul_left_comm] using hzero

/-- A determinant with fixed homogeneous row degrees has their sum as degree.
@isnad1 id=ishomoge.1h5v.s6.4a8465111be2 from=translated src=- shape=70693758 vocab=083f1e41
-/
theorem determinant_homogeneous_rows {K : Type*} [Field K] {n m : ℕ}
    (B : Matrix (Fin m) (Fin m) (Poly K n)) (δ : Fin m → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (δ i)) :
    B.det.IsHomogeneous (∑ i, δ i) := by
  classical
  rw [Matrix.det_apply]
  apply (Forms K n (∑ i, δ i)).sum_mem
  intro σ _
  have hp : (∏ i, B (σ i) i).IsHomogeneous (∑ i, δ i) := by
    have h := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => B (σ i) i)
      (fun i => δ (σ i)) (fun i _ => hB (σ i) i)
    simpa only [Equiv.sum_comp σ] using h
  change (σ.sign : ℤ) • (∏ i, B (σ i) i) ∈ (Forms K n (∑ i, δ i)).toAddSubgroup
  exact (Forms K n (∑ i, δ i)).toAddSubgroup.zsmul_mem hp (σ.sign : ℤ)

/-- The maximal minor deleting row `i` has the sum of the other row degrees.
@isnad1 id=ishomoge.1h6v.s7.6928ee5d1299 from=translated src=- shape=ff24682e vocab=907ece03
-/
theorem maximalMinor_homogeneous {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (δ : Fin (c + 1) → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (δ i)) (i : Fin (c + 1)) :
    (maximalMinor B i).IsHomogeneous (∑ j : Fin c, δ (i.succAbove j)) := by
  exact determinant_homogeneous_rows _ _ (fun j k => hB (i.succAbove j) k)

end ChoppedPlane
