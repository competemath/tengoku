module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LinearMatrix
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.ToeplitzBinary
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.ToeplitzDivision
public import Tengoku.Seed.Algebra.MvPolynomial.Division

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! An explicit rank-two linear matrix. Its coefficient proof is independent of
Steiner bundles, cohomology, and the characteristic of the coefficient field. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K]

/-- A ternary exponent vector, with coordinates in the order `x,y,z`.-/
def planeExponent (h j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 j + Finsupp.single 2 k

@[simp] theorem planeExponent_zero (h j k : ℕ) : planeExponent h j k 0 = h := by
  simp [planeExponent]
@[simp] theorem planeExponent_one (h j k : ℕ) : planeExponent h j k 1 = j := by
  simp [planeExponent]
@[simp] theorem planeExponent_two (h j k : ℕ) : planeExponent h j k 2 = k := by
  simp [planeExponent]
@[simp] theorem degree_planeExponent (h j k : ℕ) :
    (planeExponent h j k).degree = h + j + k := by
  simp [planeExponent]

theorem planeExponent_succ_x (h j k : ℕ) :
    planeExponent (h + 1) j k = Finsupp.single 0 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

theorem planeExponent_succ_y (h j k : ℕ) :
    planeExponent h (j + 1) k = Finsupp.single 1 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

theorem planeExponent_succ_z (h j k : ℕ) :
    planeExponent h j (k + 1) = Finsupp.single 2 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

@[simp] theorem coeff_x_at_x_zero (p : Poly K 3) (j k : ℕ) :
    (X 0 * p).coeff (planeExponent 0 j k) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

@[simp] theorem coeff_y_at_y_zero (p : Poly K 3) (h k : ℕ) :
    (X 1 * p).coeff (planeExponent h 0 k) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

@[simp] theorem coeff_z_at_z_zero (p : Poly K 3) (h j : ℕ) :
    (X 2 * p).coeff (planeExponent h j 0) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

@[simp] theorem coeff_y_at_y_succ (p : Poly K 3) (h j k : ℕ) :
    (X 1 * p).coeff (planeExponent h (j+1) k) = p.coeff (planeExponent h j k) := by
  rw [planeExponent_succ_y, coeff_X_mul]

@[simp] theorem coeff_z_at_z_succ (p : Poly K 3) (h j k : ℕ) :
    (X 2 * p).coeff (planeExponent h j (k+1)) = p.coeff (planeExponent h j k) := by
  rw [planeExponent_succ_z, coeff_X_mul]

/-- Every ternary exponent is the tuple of its three coordinates.-/
theorem planeExponent_coordinates (e : Fin 3 →₀ ℕ) :
    planeExponent (e 0) (e 1) (e 2) = e := by
  ext i
  fin_cases i <;> simp

/-- The actual Toeplitz matrix with row entries `x,y,z` in consecutive columns.-/
def toeplitzMatrix (K : Type*) [Field K] (a : ℕ) : LinearMatrix K a (a+2) :=
  fun i j =>
    (if j = (⟨i.val, by omega⟩ : Fin (a+2)) then ⟨X 0, isHomogeneous_X K 0⟩ else 0) +
    (if j = (⟨i.val+1, by omega⟩ : Fin (a+2)) then ⟨X 1, isHomogeneous_X K 1⟩ else 0) +
    (if j = (⟨i.val+2, by omega⟩ : Fin (a+2)) then ⟨X 2, isHomogeneous_X K 2⟩ else 0)

@[simp] theorem toeplitzMatrix_val {a : ℕ} (i : Fin a) (j : Fin (a+2)) :
    (toeplitzMatrix K a i j).val =
      (if j = (⟨i.val, by omega⟩ : Fin (a+2)) then X 0 else 0) +
      (if j = (⟨i.val+1, by omega⟩ : Fin (a+2)) then X 1 else 0) +
      (if j = (⟨i.val+2, by omega⟩ : Fin (a+2)) then X 2 else 0) := by
  classical
  unfold toeplitzMatrix
  split_ifs <;> rfl

@[simp] theorem toeplitzMatrix_map_val {a t : ℕ}
    (v : MatrixSource K (a+2) t) (i : Fin a) :
    (linearMatrixMap (toeplitzMatrix K a) t v i).val =
      X 0 * (v ⟨i.val, by omega⟩).val +
      X 1 * (v ⟨i.val+1, by omega⟩).val +
      X 2 * (v ⟨i.val+2, by omega⟩).val := by
  classical
  simp only [linearMatrixMap_val, toeplitzMatrix_val, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib]
  simp

end ChoppedPlane
