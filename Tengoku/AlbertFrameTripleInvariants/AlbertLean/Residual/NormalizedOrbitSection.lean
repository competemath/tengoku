import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.SL4PairAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @ResidualSL4NormalizedSectionTheorem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms det_X0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms X0_mul_X0Inv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalizingDetOneMatrix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms act_normalizingDetOneMatrix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalizingMatrix_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms transitionDetOneMatrix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms act_transitionDetOneMatrix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms related_iff_same_moment_delta` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ResidualSL4NormalizedSectionTheorem` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Normalized determinant chart for the explicit residual action

On the principal chart `det X != 0`, this module normalizes the vector-column
matrix to

`X0(Delta) = diag(1, 1, 1, Delta)`.

The explicit normalizer is `g = X0(Delta) * X^-1`, with specified inverse
`gInv = X * X0Inv(Delta)`.  The transformed covector-row matrix is therefore
`M * X0Inv(Delta)`.  The resulting theorem is a chart-level orbit
classification for the explicit matrix action only.  It makes no `Spin(6) =
SL4`, invariant-ring, global quotient, or deck claim.
-/

namespace AlbertLean.Residual.NormalizedOrbitSection

open Matrix
open AlbertLean.Residual.SL4PairAction

universe u

noncomputable section

variable {K : Type u} [Field K]

/-- the frozen normalized vector-column
matrix `diag(1,1,1,Delta)`.-/
def X0 (Delta : K) : Mat4 K :=
  Matrix.diagonal ![1, 1, 1, Delta]

/-- the displayed inverse candidate
`diag(1,1,1,Delta^-1)`.-/
def X0Inv (Delta : K) : Mat4 K :=
  Matrix.diagonal ![1, 1, 1, Delta⁻¹]

/-- the determinant of the normalized
matrix is its displayed final diagonal coordinate.
@isnad1 id=eq.0h2v.s5.a3c813d5b611 from=translated src=- shape=06018280 vocab=932e9eeb
-/
@[simp] theorem det_X0 (Delta : K) : Matrix.det (X0 Delta) = Delta := by
  simp [X0, Matrix.det_diagonal, Fin.prod_univ_succ]

/-- the determinant of the inverse
candidate is the inverse scalar.
@isnad1 id=eq.0h2v.s5.edaba780540a from=translated src=- shape=1fae67e4 vocab=cf67e583
-/
@[simp] theorem det_X0Inv (Delta : K) :
    Matrix.det (X0Inv Delta) = Delta⁻¹ := by
  simp [X0Inv, Matrix.det_diagonal, Fin.prod_univ_succ]

/-- the normalized diagonal matrix
multiplies its inverse candidate to one when `Delta` is nonzero.
@isnad1 id=eq.1h2v.s7.169ab13affa2 from=translated src=- shape=bd6c35ad vocab=48663cd3
-/
theorem X0_mul_X0Inv (Delta : K) (hDelta : Delta ≠ 0) :
    X0 Delta * X0Inv Delta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X0, X0Inv, Matrix.mul_apply, Fin.sum_univ_succ, hDelta]

/-- the inverse candidate also
multiplies the normalized diagonal matrix to one.
@isnad1 id=eq.1h2v.s7.8acf280fed46 from=translated src=- shape=bd6c35ad vocab=48663cd3
-/
theorem X0Inv_mul_X0 (Delta : K) (hDelta : Delta ≠ 0) :
    X0Inv Delta * X0 Delta = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X0, X0Inv, Matrix.mul_apply, Fin.sum_univ_succ, hDelta]

/-- the normalizing matrix
`X0(det X) * X^-1`.-/
def normalizingMatrix (P : ResidualPair K) : Mat4 K :=
  X0 (delta P) * P.X⁻¹

/-- the specified inverse of the
normalizing matrix, `X * X0Inv(det X)`.-/
def normalizingMatrixInv (P : ResidualPair K) : Mat4 K :=
  P.X * X0Inv (delta P)

/-- the normalized representative with
the same `M` and `Delta`.-/
def normalizedPair (P : ResidualPair K) : ResidualPair K where
  A := moment P * X0Inv (delta P)
  X := X0 (delta P)

/-- on `det X != 0`, the
displayed matrix and inverse form a lawful determinant-one action witness.-/
def normalizingDetOneMatrix (P : ResidualPair K) (hX : delta P ≠ 0) :
    DetOneMatrix K where
  g := normalizingMatrix P
  gInv := normalizingMatrixInv P
  g_mul_gInv := by
    rw [normalizingMatrix, normalizingMatrixInv, Matrix.mul_assoc,
      ← Matrix.mul_assoc P.X⁻¹ P.X (X0Inv (delta P)),
      Matrix.nonsing_inv_mul P.X (isUnit_iff_ne_zero.mpr hX),
      Matrix.one_mul, X0_mul_X0Inv (delta P) hX]
  gInv_mul_g := by
    rw [normalizingMatrix, normalizingMatrixInv, Matrix.mul_assoc,
      ← Matrix.mul_assoc (X0Inv (delta P)) (X0 (delta P)) P.X⁻¹,
      X0Inv_mul_X0 (delta P) hX, Matrix.one_mul,
      Matrix.mul_nonsing_inv P.X (isUnit_iff_ne_zero.mpr hX)]
  det_g := by
    rw [normalizingMatrix, Matrix.det_mul, det_X0, mul_comm]
    exact Matrix.det_nonsing_inv_mul_det P.X
      (isUnit_iff_ne_zero.mpr hX)

/-- the declared action of the
normalizing witness sends the pair to its displayed normalized
representative.
@isnad1 id=eq.1h2v.s5.bf2172b1385e from=translated src=- shape=d6916534 vocab=2cdef200
-/
theorem act_normalizingDetOneMatrix (P : ResidualPair K)
    (hX : delta P ≠ 0) :
    act (normalizingDetOneMatrix P hX) P = normalizedPair P := by
  apply ResidualPair.ext
  · simp only [act_A, normalizingDetOneMatrix, normalizingMatrixInv,
      normalizedPair, moment]
    rw [← Matrix.mul_assoc]
  · simp only [act_X, normalizingDetOneMatrix, normalizingMatrix,
      normalizedPair]
    rw [Matrix.mul_assoc,
      Matrix.nonsing_inv_mul P.X (isUnit_iff_ne_zero.mpr hX),
      Matrix.mul_one]

/-- the normalizing matrix is uniquely
determined by the equation `g * X = X0(det X)`.  This is uniqueness of the
matrix `g`, not a global orbit representative.
@isnad1 id=eq.2h3v.s7.8adb4742fb23 from=translated src=- shape=fc33932e vocab=681eba0e
-/
theorem normalizingMatrix_unique (P : ResidualPair K) (hX : delta P ≠ 0)
    (g : Mat4 K) (hg : g * P.X = X0 (delta P)) :
    g = normalizingMatrix P := by
  calc
    g = g * (P.X * P.X⁻¹) := by
      rw [Matrix.mul_nonsing_inv P.X (isUnit_iff_ne_zero.mpr hX),
        Matrix.mul_one]
    _ = (g * P.X) * P.X⁻¹ := by rw [Matrix.mul_assoc]
    _ = normalizingMatrix P := by rw [hg]; rfl

/-- the transition matrix carrying
`P.X` to `Q.X` on the invertible-`X` chart.-/
def transitionMatrix (P Q : ResidualPair K) : Mat4 K :=
  Q.X * P.X⁻¹

/-- the specified inverse transition
matrix.-/
def transitionMatrixInv (P Q : ResidualPair K) : Mat4 K :=
  P.X * Q.X⁻¹

/-- equality of `(M, Delta)` constructs
the explicit determinant-one transition action between two invertible-`X`
pairs.-/
def transitionDetOneMatrix (P Q : ResidualPair K)
    (hP : delta P ≠ 0) (hQ : delta Q ≠ 0)
    (hM : moment P = moment Q) (hDelta : delta P = delta Q) :
    DetOneMatrix K where
  g := transitionMatrix P Q
  gInv := transitionMatrixInv P Q
  g_mul_gInv := by
    rw [transitionMatrix, transitionMatrixInv, Matrix.mul_assoc,
      ← Matrix.mul_assoc P.X⁻¹ P.X Q.X⁻¹,
      Matrix.nonsing_inv_mul P.X (isUnit_iff_ne_zero.mpr hP),
      Matrix.one_mul, Matrix.mul_nonsing_inv Q.X
        (isUnit_iff_ne_zero.mpr hQ)]
  gInv_mul_g := by
    rw [transitionMatrix, transitionMatrixInv, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q.X⁻¹ Q.X P.X⁻¹,
      Matrix.nonsing_inv_mul Q.X (isUnit_iff_ne_zero.mpr hQ),
      Matrix.one_mul, Matrix.mul_nonsing_inv P.X
        (isUnit_iff_ne_zero.mpr hP)]
  det_g := by
    rw [transitionMatrix, Matrix.det_mul]
    have hdet : Matrix.det P.X = Matrix.det Q.X := hDelta
    rw [← hdet, mul_comm]
    exact Matrix.det_nonsing_inv_mul_det P.X
      (isUnit_iff_ne_zero.mpr hP)

/-- the explicit transition witness
constructed from equal `(M, Delta)` invariants carries `P` to `Q`.
@isnad1 id=eq.4h3v.s6.90c4be86b5e1 from=translated src=- shape=45431f42 vocab=0314c903
-/
theorem act_transitionDetOneMatrix (P Q : ResidualPair K)
    (hP : delta P ≠ 0) (hQ : delta Q ≠ 0)
    (hM : moment P = moment Q) (hDelta : delta P = delta Q) :
    act (transitionDetOneMatrix P Q hP hQ hM hDelta) P = Q := by
  apply ResidualPair.ext
  · simp only [act_A, transitionDetOneMatrix, transitionMatrixInv]
    calc
      P.A * (P.X * Q.X⁻¹) = moment P * Q.X⁻¹ := by
        rw [moment, ← Matrix.mul_assoc]
      _ = moment Q * Q.X⁻¹ := by rw [hM]
      _ = Q.A := by
        rw [moment, Matrix.mul_nonsing_inv_cancel_right Q.X Q.A
          (isUnit_iff_ne_zero.mpr hQ)]
  · simp only [act_X, transitionDetOneMatrix, transitionMatrix]
    rw [Matrix.mul_assoc,
      Matrix.nonsing_inv_mul P.X (isUnit_iff_ne_zero.mpr hP),
      Matrix.mul_one]

/-- on the invertible-`X` chart,
explicit orbit relatedness is equivalent to equality of the pairing matrix
and `Delta`.
@isnad1 id=iff.2h3v.s6.67348f22551a from=translated src=- shape=7b7fa7b3 vocab=757f0852
-/
theorem related_iff_same_moment_delta (P Q : ResidualPair K)
    (hP : delta P ≠ 0) (hQ : delta Q ≠ 0) :
    Related P Q ↔ moment P = moment Q ∧ delta P = delta Q := by
  constructor
  · intro h
    exact ⟨(related_preserves_invariants h).1,
      (related_preserves_invariants h).2.1⟩
  · rintro ⟨hM, hDelta⟩
    exact ⟨transitionDetOneMatrix P Q hP hQ hM hDelta,
      act_transitionDetOneMatrix P Q hP hQ hM hDelta⟩

/-- every residual pair with
invertible `X` has the displayed determinant-one normalized representative;
the normalizing matrix is unique, and `(M, Delta)` exactly classifies the
explicit orbits on this chart.
@isnad1 id=other.1h2v.s8.4a09b7b4eaa8 from=translated src=- shape=c00ce165 vocab=5f716977
-/
theorem ResidualSL4NormalizedSectionTheorem
    (P : ResidualPair K) (hP : delta P ≠ 0) :
    let G := normalizingDetOneMatrix P hP
    Matrix.det G.g = 1 ∧
      act G P = normalizedPair P ∧
      (∀ g : Mat4 K, g * P.X = X0 (delta P) → g = G.g) ∧
      (∀ Q : ResidualPair K, delta Q ≠ 0 →
        (Related P Q ↔ moment P = moment Q ∧ delta P = delta Q)) := by
  dsimp
  exact ⟨(normalizingDetOneMatrix P hP).det_g,
    act_normalizingDetOneMatrix P hP,
    fun g hg => normalizingMatrix_unique P hP g hg,
    fun Q hQ => related_iff_same_moment_delta P Q hP hQ⟩

end

end AlbertLean.Residual.NormalizedOrbitSection
