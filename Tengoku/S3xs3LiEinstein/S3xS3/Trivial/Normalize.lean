import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.Gauge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Normalize

open S3xS3.Trivial.Graph
open S3xS3.Trivial.Euler
open S3xS3.Trivial.Gauge

/--
@isnad1 id=eq.0h3v.s5.e15c004d44ba from=translated src=- shape=ce527358 vocab=e0704a01
-/
lemma dcof_smul_left (t : ℝ) (A H : Mat3) :
    dcof (t • A) H = t • dcof A H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dcof] <;> ring

/--
@isnad1 id=eq.0h3v.s5.29e44163ce91 from=translated src=- shape=b5dd2775 vocab=e0704a01
-/
lemma dcof_smul_right (t : ℝ) (A H : Mat3) :
    dcof A (t • H) = t • dcof A H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dcof] <;> ring

/--
@isnad1 id=eq.0h4v.s6.6978ac55b2d8 from=translated src=- shape=a59be4bb vocab=f5fe6f7d
-/
lemma residual_scale (t : ℝ) (P Q M : Mat3) :
    Euler.residual (t • P) (t • Q) M =
      t • Euler.residual P Q M := by
  simp only [Euler.residual, Matrix.mul_smul, Matrix.smul_mul]
  module

/--
@isnad1 id=eq.0h2v.s5.9b87314b1f8c from=translated src=- shape=f90c5dad vocab=bf78cd59
-/
lemma lop'_scale (t : ℝ) (P : Mat3) :
    lop' (t • P) = t ^ 2 • lop' P := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lop', cofactor3, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

/--
@isnad1 id=eq.0h4v.s6.9f8dd2f089b5 from=translated src=- shape=a59be4bb vocab=1443c828
-/
lemma gradPFormula_scale (t : ℝ) (P Q M : Mat3) :
    gradPFormula (t • P) (t • Q) M = t • gradPFormula P Q M := by
  rw [gradPFormula, gradPFormula, residual_scale, dcof_smul_left]
  simp only [Matrix.trace_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.transpose_smul, smul_smul]
  module

/--
@isnad1 id=eq.0h4v.s6.4ecb3788bc6b from=translated src=- shape=a59be4bb vocab=62b13a3a
-/
lemma gradQFormula_scale (t : ℝ) (P Q M : Mat3) :
    gradQFormula (t • P) (t • Q) M = t • gradQFormula P Q M := by
  rw [gradQFormula, gradQFormula, residual_scale]
  simp only [Matrix.trace_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.transpose_smul, smul_smul]
  module

/--
@isnad1 id=eq.0h4v.s6.237e973c1640 from=translated src=- shape=3d451980 vocab=126847a9
-/
lemma gradMFormula_scale (t : ℝ) (P Q M : Mat3) :
    gradMFormula (t • P) (t • Q) M = t ^ 2 • gradMFormula P Q M := by
  rw [gradMFormula, gradMFormula, lop'_scale, residual_scale]
  have hRP :
      (t • Euler.residual P Q M) * (t • P) =
        t ^ 2 • (Euler.residual P Q M * P) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    ring
  rw [hRP, dcof_smul_right]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  module

/--
@isnad1 id=eq.2h2v.s6.35f832cb86d4 from=translated src=- shape=9d427b59 vocab=3447a707
-/
lemma nonsing_inv_smul {t : ℝ} (ht : t ≠ 0) (A : Mat3)
    (hA : IsUnit A.det) :
    (t • A)⁻¹ = (t⁻¹ : ℝ) • A⁻¹ := by
  letI : Invertible t := invertibleOfNonzero ht
  calc
    (t • A)⁻¹ = ⅟t • A⁻¹ := Matrix.inv_smul A t hA
    _ = (t⁻¹ : ℝ) • A⁻¹ := by rw [invOf_eq_inv]

noncomputable def EulerData.scale (d : EulerData) (t : ℝ) (ht : 0 < t) :
    EulerData where
  P := t • d.P
  Q := t • d.Q
  M := d.M
  kappa := t ^ 2 * d.kappa
  P_pos := d.P_pos.smul ht
  Q_pos := d.Q_pos.smul ht
  kappa_pos := mul_pos (sq_pos_of_pos ht) d.kappa_pos
  gradP := by
    change gradPFormula (t • d.P) (t • d.Q) d.M =
      (t ^ 2 * d.kappa) • (t • d.P)⁻¹
    rw [gradPFormula_scale]
    have hdet : IsUnit d.P.det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt d.P_pos.det_pos)
    rw [nonsing_inv_smul (ne_of_gt ht) d.P hdet]
    have hd : gradPFormula d.P d.Q d.M = d.kappa • d.P⁻¹ := d.gradP
    rw [hd, smul_smul, smul_smul]
    congr 1
    field_simp [ne_of_gt ht]
  gradQ := by
    change gradQFormula (t • d.P) (t • d.Q) d.M =
      (t ^ 2 * d.kappa) • (t • d.Q)⁻¹
    rw [gradQFormula_scale]
    have hdet : IsUnit d.Q.det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt d.Q_pos.det_pos)
    rw [nonsing_inv_smul (ne_of_gt ht) d.Q hdet]
    have hd : gradQFormula d.P d.Q d.M = d.kappa • d.Q⁻¹ := d.gradQ
    rw [hd, smul_smul, smul_smul]
    congr 1
    field_simp [ne_of_gt ht]
  gradM := by
    change gradMFormula (t • d.P) (t • d.Q) d.M = 0
    rw [gradMFormula_scale]
    have hd : gradMFormula d.P d.Q d.M = 0 := d.gradM
    rw [hd, smul_zero]

noncomputable def EulerData.normalize (d : EulerData) : EulerData :=
  EulerData.scale d (rhoP d) (rhoP_pos d)

/--
@isnad1 id=eq.0h1v.s3.de29077c92d1 from=translated src=- shape=8d4cac31 vocab=e8820374
-/
lemma normalize_M (d : EulerData) : (EulerData.normalize d).M = d.M := rfl

end S3xS3.Trivial.Normalize
