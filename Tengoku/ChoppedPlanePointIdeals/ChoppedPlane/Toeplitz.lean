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

/--
@isnad1 id=eq.0h3v.s6.819a28c00985 from=translated src=- shape=ec88752e vocab=b2979009
-/
@[simp] theorem planeExponent_zero (h j k : ℕ) : planeExponent h j k 0 = h := by
  simp [planeExponent]
/--
@isnad1 id=eq.0h3v.s6.203ee0e638b9 from=translated src=- shape=dcf1bd0f vocab=b2979009
-/
@[simp] theorem planeExponent_one (h j k : ℕ) : planeExponent h j k 1 = j := by
  simp [planeExponent]
/--
@isnad1 id=eq.0h3v.s6.dc983c0f4df8 from=translated src=- shape=db502428 vocab=b2979009
-/
@[simp] theorem planeExponent_two (h j k : ℕ) : planeExponent h j k 2 = k := by
  simp [planeExponent]
/--
@isnad1 id=eq.0h3v.s7.9830dba6f1b6 from=translated src=- shape=10dd35f9 vocab=8c062a58
-/
@[simp] theorem degree_planeExponent (h j k : ℕ) :
    (planeExponent h j k).degree = h + j + k := by
  simp [planeExponent]

/--
@isnad1 id=eq.0h3v.s6.e90eb5ea64c1 from=translated src=- shape=03bf5386 vocab=63fcc696
-/
theorem planeExponent_succ_x (h j k : ℕ) :
    planeExponent (h + 1) j k = Finsupp.single 0 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

/--
@isnad1 id=eq.0h3v.s6.96934ea9c833 from=translated src=- shape=e494b02b vocab=63fcc696
-/
theorem planeExponent_succ_y (h j k : ℕ) :
    planeExponent h (j + 1) k = Finsupp.single 1 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

/--
@isnad1 id=eq.0h3v.s6.d65033b2e824 from=translated src=- shape=521257ff vocab=63fcc696
-/
theorem planeExponent_succ_z (h j k : ℕ) :
    planeExponent h j (k + 1) = Finsupp.single 2 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

/--
@isnad1 id=eq.0h4v.s7.98c3e2c28a78 from=translated src=- shape=8e499d7c vocab=d1741377
-/
@[simp] theorem coeff_x_at_x_zero (p : Poly K 3) (j k : ℕ) :
    (X 0 * p).coeff (planeExponent 0 j k) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

/--
@isnad1 id=eq.0h4v.s7.66f768eee400 from=translated src=- shape=2ca4fd28 vocab=d1741377
-/
@[simp] theorem coeff_y_at_y_zero (p : Poly K 3) (h k : ℕ) :
    (X 1 * p).coeff (planeExponent h 0 k) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

/--
@isnad1 id=eq.0h4v.s7.830c52c66ede from=translated src=- shape=bee64e9c vocab=d1741377
-/
@[simp] theorem coeff_z_at_z_zero (p : Poly K 3) (h j : ℕ) :
    (X 2 * p).coeff (planeExponent h j 0) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

/--
@isnad1 id=eq.0h5v.s7.98bd8887559d from=translated src=- shape=dd9d6517 vocab=3491d197
-/
@[simp] theorem coeff_y_at_y_succ (p : Poly K 3) (h j k : ℕ) :
    (X 1 * p).coeff (planeExponent h (j+1) k) = p.coeff (planeExponent h j k) := by
  rw [planeExponent_succ_y, coeff_X_mul]

/--
@isnad1 id=eq.0h5v.s7.701a757274f6 from=translated src=- shape=cfe98e9f vocab=3491d197
-/
@[simp] theorem coeff_z_at_z_succ (p : Poly K 3) (h j k : ℕ) :
    (X 2 * p).coeff (planeExponent h j (k+1)) = p.coeff (planeExponent h j k) := by
  rw [planeExponent_succ_z, coeff_X_mul]

/-- Every ternary exponent is the tuple of its three coordinates.
@isnad1 id=eq.0h1v.s7.7f5c766facc2 from=translated src=- shape=9a71e463 vocab=b2979009
-/
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

/--
@isnad1 id=eq.0h4v.s10.c9a6a34bff91 from=translated src=- shape=50d29fbc vocab=08eb509a
-/
@[simp] theorem toeplitzMatrix_val {a : ℕ} (i : Fin a) (j : Fin (a+2)) :
    (toeplitzMatrix K a i j).val =
      (if j = (⟨i.val, by omega⟩ : Fin (a+2)) then X 0 else 0) +
      (if j = (⟨i.val+1, by omega⟩ : Fin (a+2)) then X 1 else 0) +
      (if j = (⟨i.val+2, by omega⟩ : Fin (a+2)) then X 2 else 0) := by
  classical
  unfold toeplitzMatrix
  split_ifs <;> rfl

/--
@isnad1 id=eq.0h5v.s12.2b0aad69909e from=translated src=- shape=be0a42cf vocab=864ef488
-/
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
