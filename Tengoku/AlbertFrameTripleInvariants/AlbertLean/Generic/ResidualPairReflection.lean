import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Residual.NormalizedOrbitSection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms moment_reflect` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms delta_reflect` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms delta_reflect_normalizedPair` (it only prints; the queue checks the axioms of every declaration). -/

/-!
This file isolates only the residual-pair matrix
reflection needed by the detector-descent construction.  It does not define
the coordinate reflection on the Albert source space.
-/

noncomputable section

namespace AlbertLean.Residual.ResidualPairReflection

open Matrix
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Residual.NormalizedOrbitSection

universe u

variable {K : Type u} [Field K] [CharZero K]

def D (a : K) : Mat4 K := Matrix.diagonal ![a⁻¹, a⁻¹, 1, 1]
def Di (a : K) : Mat4 K := Matrix.diagonal ![a, a, 1, 1]
def L (a : K) : Mat4 K := Matrix.diagonal ![1, 1, a, a]
def Li (a : K) : Mat4 K := Matrix.diagonal ![1, 1, a⁻¹, a⁻¹]

def reflectionWeight (a : K) : Fin 4 → K := ![1, 1, a, a]

theorem Li_transpose_mul_L_apply (a : K) (M : Mat4 K) (i j : Fin 4) :
    (Li a * M.transpose * L a) i j =
      (reflectionWeight a i)⁻¹ * reflectionWeight a j * M j i := by
  fin_cases i <;> fin_cases j <;>
    simp [Li, L, reflectionWeight, Matrix.diagonal_mul, Matrix.mul_diagonal] <;> ring

theorem Di_mul_D (a : K) (ha : a ≠ 0) : Di a * D a = 1 := by
  rw [Di, D, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha]

theorem L_mul_Li (a : K) (ha : a ≠ 0) : L a * Li a = 1 := by
  rw [L, Li, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha]

theorem Li_mul_L (a : K) (ha : a ≠ 0) : Li a * L a = 1 := by
  rw [Li, L, Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha]

/-- Reflection of the residual matrix pair induced by the corrected source
coordinate reflection.-/
def reflect (a : K) (P : ResidualPair K) : ResidualPair K where
  X := D a * P.A.transpose * L a
  A := Li a * P.X.transpose * Di a

/-- The reflected moment is weighted transposition of the original moment.-/
theorem moment_reflect (a : K) (ha : a ≠ 0) (P : ResidualPair K) :
    moment (reflect a P) = Li a * (moment P).transpose * L a := by
  simp only [moment, reflect, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Di a) (D a), Di_mul_D a ha, Matrix.one_mul]

theorem moment_reflect_apply (a : K) (ha : a ≠ 0)
    (P : ResidualPair K) (i j : Fin 4) :
    moment (reflect a P) i j =
      (reflectionWeight a i)⁻¹ * reflectionWeight a j * moment P j i := by
  rw [moment_reflect a ha, Li_transpose_mul_L_apply]

private theorem det_D_mul_det_L (a : K) (ha : a ≠ 0) :
    Matrix.det (D a) * Matrix.det (L a) = 1 := by
  simp [D, L, Matrix.det_diagonal, Fin.prod_univ_succ]
  calc
    a⁻¹ * a⁻¹ * (a * a) = (a⁻¹ * a) * (a⁻¹ * a) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ ha]; simp

/-- Reflection exchanges the vector determinant with the covector
determinant.-/
theorem delta_reflect (a : K) (ha : a ≠ 0) (P : ResidualPair K) :
    delta (reflect a P) = Matrix.det P.A := by
  simp only [delta, reflect, Matrix.det_mul, Matrix.det_transpose]
  calc
    Matrix.det (D a) * Matrix.det P.A * Matrix.det (L a) =
        (Matrix.det (D a) * Matrix.det (L a)) * Matrix.det P.A := by ring
    _ = Matrix.det P.A := by rw [det_D_mul_det_L a ha, one_mul]

/-- A normalized residual pair has covector determinant `det(moment)/t`.
This is the generic normalization readback used after `t = delta P`.-/
theorem deltaStar_normalizedPair (P : ResidualPair K) (hP : delta P ≠ 0) :
    deltaStar (normalizedPair P) = Matrix.det (moment P) / delta P := by
  simp only [deltaStar, normalizedPair, Matrix.det_mul, det_X0Inv,
    div_eq_mul_inv]

/-- Consequently reflection sends the normalized vector determinant to the
other root `det(moment P) / delta P`.-/
theorem delta_reflect_normalizedPair (a : K) (ha : a ≠ 0)
    (P : ResidualPair K) (hP : delta P ≠ 0) :
    delta (reflect a (normalizedPair P)) =
      Matrix.det (moment P) / delta P := by
  rw [delta_reflect a ha]
  exact deltaStar_normalizedPair P hP

end AlbertLean.Residual.ResidualPairReflection
