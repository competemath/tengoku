import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Modules.OrientedMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Modules/TensorMatrix.lean
  Tensors as matrices over K_M, ⋆_M-product of tensors.

  Figure 2: The squeeze/twist isomorphisms between K_M^m and ℝ^{m×n}.
  - squeeze: K_M^m → ℝ^{m×n}  (lay out each tube as a row)
  - twist:   ℝ^{m×n} → K_M^m  (twist each row into a tube)

  A third-order tensor A ∈ ℝ^{m×p×n} is identified with a matrix
  A ∈ K_M^{m×p} = Matrix (Fin m) (Fin p) (KM n td).

  The ⋆_M-product of two tensors A ∈ K_M^{m×p} and B ∈ K_M^{p×l}
  is the matrix product (A * B) ∈ K_M^{m×l}, using the CommRing
  instance on KM for the entry-level multiplications.
-/

namespace TubalTensor

variable {n : ℕ} {td : TubalData n} {m p l : ℕ}

/-! ## Squeeze and twist for oriented matrices (Figure 2)

  K_M^m ≅ ℝ^{m×n}: each oriented matrix (m-tuple of n-tubes) corresponds
  to an m × n real matrix, where the i-th row is the i-th tube.
  - `squeeze`: K_M^m → ℝ^{m×n} (flatten tubes into rows)
  - `twist`:   ℝ^{m×n} → K_M^m (twist rows into tubes) -/

/-- Squeeze: extract an m × n real matrix from an oriented matrix (Figure 2).
    Row i of the output is the i-th tube.-/
def squeeze (U : OrientedMatrix m n td) : Matrix (Fin m) (Fin n) ℝ :=
  fun i k => KM.toFun (U i) k

/-- Twist: wrap an m × n real matrix into an oriented matrix (Figure 2).
    Row i becomes the i-th tube.-/
def twist (M : Matrix (Fin m) (Fin n) ℝ) : OrientedMatrix m n td :=
  fun i => KM.ofFun (M i)

@[simp]
theorem squeeze_twist (M : Matrix (Fin m) (Fin n) ℝ) :
    squeeze (twist M : OrientedMatrix m n td) = M := rfl

@[simp]
theorem twist_squeeze (U : OrientedMatrix m n td) :
    twist (squeeze U) = U := by
  funext i; rfl

/-! ## Tubal matrices: matrices over K_M -/

/-- A tubal matrix (third-order tensor viewed as a matrix over K_M).
    The ⋆_M-product is inherited from `Matrix.mul` via the `CommRing` instance.-/
abbrev TubalMatrix (m p : ℕ) (n : ℕ) (td : TubalData n) :=
  Matrix (Fin m) (Fin p) (KM n td)

/-! ## The identity tubal matrix

  I_m has eM on the diagonal and 0 elsewhere.
  This is just `(1 : Matrix (Fin m) (Fin m) (KM n td))`. -/

/-- The identity tubal matrix is the Mathlib matrix identity.-/
theorem tubalMatrix_one_eq :
    (1 : TubalMatrix m m n td) = Matrix.diagonal (fun _ => 1) := by
  ext i j; simp [Matrix.one_apply, Matrix.diagonal_apply]

end TubalTensor
