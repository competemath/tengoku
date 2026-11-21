import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.Graph
import Tengoku.S3xs3LiEinstein.S3xS3.Trivial.SupportExclusion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix MatrixOrder BigOperators

namespace S3xS3.Trivial.Euler

open S3xS3.Trivial.Graph

def frob (A B : Mat3) : ℝ := ∑ i, ∑ j, A i j * B i j

def frobNormSq (A : Mat3) : ℝ := frob A A

/--
@isnad1 id=eq.0h4v.s5.745dfb4da2fe from=translated src=- shape=c0f66342 vocab=6c8753c1
-/
@[simp] lemma real_smul_apply (c : ℝ) (A : Mat3) (i j : I3) :
    (c • A) i j = c * A i j := rfl

def dcof (A H : Mat3) : Mat3 :=
  !![H 1 1 * A 2 2 + A 1 1 * H 2 2 - H 1 2 * A 2 1 - A 1 2 * H 2 1,
     H 1 2 * A 2 0 + A 1 2 * H 2 0 - H 1 0 * A 2 2 - A 1 0 * H 2 2,
     H 1 0 * A 2 1 + A 1 0 * H 2 1 - H 1 1 * A 2 0 - A 1 1 * H 2 0;
     H 0 2 * A 2 1 + A 0 2 * H 2 1 - H 0 1 * A 2 2 - A 0 1 * H 2 2,
     H 0 0 * A 2 2 + A 0 0 * H 2 2 - H 0 2 * A 2 0 - A 0 2 * H 2 0,
     H 0 1 * A 2 0 + A 0 1 * H 2 0 - H 0 0 * A 2 1 - A 0 0 * H 2 1;
     H 0 1 * A 1 2 + A 0 1 * H 1 2 - H 0 2 * A 1 1 - A 0 2 * H 1 1,
     H 0 2 * A 1 0 + A 0 2 * H 1 0 - H 0 0 * A 1 2 - A 0 0 * H 1 2,
     H 0 0 * A 1 1 + A 0 0 * H 1 1 - H 0 1 * A 1 0 - A 0 1 * H 1 0]

def lop (P : Mat3) : Mat3 :=
  P.trace • (P.trace • (1 : Mat3)) - (2 : ℝ) • (P * P) -
    (2 : ℝ) • cofactor3 P

-- Equivalent to the manuscript's `tr(P^2) I - P^2 - 2 cof(P)`.
def lop' (P : Mat3) : Mat3 :=
  (P * P).trace • (1 : Mat3) - P * P - (2 : ℝ) • cofactor3 P

def kop (H : Mat3) : Mat3 :=
  cofactor3 H - (2 : ℝ) • (H.trace • (1 : Mat3)) + (4 : ℝ) • H

def residual (P Q M : Mat3) : Mat3 := cofactor3 M * P - Q * M

structure EulerData where
  P : Mat3
  Q : Mat3
  M : Mat3
  kappa : ℝ
  P_pos : P.PosDef
  Q_pos : Q.PosDef
  kappa_pos : 0 < kappa
  gradP :
    P.trace • (1 : Mat3) - (2 : ℝ) • P -
        (Mᵀ * M).trace • P +
        (1 / 2 : ℝ) • (Mᵀ * M * P + P * (Mᵀ * M)) +
        dcof P (Mᵀ * M) -
        (1 / 2 : ℝ) •
          ((cofactor3 M)ᵀ * residual P Q M +
            ((cofactor3 M)ᵀ * residual P Q M)ᵀ) =
      kappa • P⁻¹
  gradQ :
    Q.trace • (1 : Mat3) - (2 : ℝ) • Q +
        (1 / 2 : ℝ) •
          (residual P Q M * Mᵀ + M * (residual P Q M)ᵀ) =
      kappa • Q⁻¹
  gradM :
    -(M * lop' P) - dcof M (residual P Q M * P) +
        Q * residual P Q M = 0

/--
@isnad1 id=eq.1h1v.s6.48c4ef1b5e57 from=translated src=- shape=1b7b9313 vocab=8b4388fc
-/
lemma cofactor3_eq_det_smul_inv {A : Mat3} (hA : A.PosDef) :
    cofactor3 A = A.det • A⁻¹ := by
  have hAu : IsUnit A := hA.isUnit
  have hAtu : IsUnit Aᵀ := (Matrix.isUnit_transpose A).2 hAu
  have hAdetu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  apply hAtu.mul_right_cancel
  rw [cofactor3_mul_transpose]
  have hAt : Aᵀ = A := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  rw [hAt]
  calc
    A.det • (1 : Mat3) = A.det • (A⁻¹ * A) := by
      rw [A.nonsing_inv_mul hAdetu]
    _ = (A.det • A⁻¹) * A := by rw [Matrix.smul_mul]

noncomputable def rhoP (d : EulerData) : ℝ := 2 * d.kappa / d.P.det
noncomputable def rhoQ (d : EulerData) : ℝ := 2 * d.kappa / d.Q.det

/--
@isnad1 id=lt.0h1v.s3.120b5c34571d from=translated src=- shape=b9369acb vocab=b424ccba
-/
lemma rhoP_pos (d : EulerData) : 0 < rhoP d := by
  exact div_pos (mul_pos two_pos d.kappa_pos) d.P_pos.det_pos

/--
@isnad1 id=lt.0h1v.s3.0fe32626e190 from=translated src=- shape=b9369acb vocab=e8da2648
-/
lemma rhoQ_pos (d : EulerData) : 0 < rhoQ d := by
  exact div_pos (mul_pos two_pos d.kappa_pos) d.Q_pos.det_pos

def alpha (d : EulerData) : ℝ :=
  frob (residual d.P d.Q d.M) (cofactor3 d.M * d.P)

def ell (d : EulerData) : ℝ := ((d.Mᵀ * d.M) * lop' d.P).trace

def beta (d : EulerData) : ℝ :=
  frob (residual d.P d.Q d.M) (d.Q * d.M)

def radialXsq (d : EulerData) : ℝ :=
  frobNormSq (cofactor3 d.M * d.P)

def radialYsq (d : EulerData) : ℝ :=
  frobNormSq (d.Q * d.M)

def radialPair (d : EulerData) : ℝ :=
  frob (cofactor3 d.M * d.P) (d.Q * d.M)

noncomputable def radialX (d : EulerData) : ℝ := Real.sqrt (radialXsq d)

noncomputable def radialY (d : EulerData) : ℝ := Real.sqrt (radialYsq d)

/--
@isnad1 id=le.0h1v.s3.bb2c96b4f1ca from=translated src=- shape=b9369acb vocab=603acafc
-/
lemma frobNormSq_nonneg (A : Mat3) : 0 ≤ frobNormSq A := by
  simp only [frobNormSq, frob]
  exact Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

/--
@isnad1 id=iff.0h1v.s4.d9b195904717 from=translated src=- shape=3a75f94e vocab=5869e69f
-/
lemma frobNormSq_eq_zero_iff (A : Mat3) : frobNormSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [frobNormSq, frob, Fin.sum_univ_succ] at h ⊢ <;> nlinarith
  · rintro rfl
    simp [frobNormSq, frob]

/--
@isnad1 id=le.0h1v.s3.9e62b7872265 from=translated src=- shape=b9369acb vocab=52b61162
-/
lemma radialX_nonneg (d : EulerData) : 0 ≤ radialX d := Real.sqrt_nonneg _

/--
@isnad1 id=le.0h1v.s3.6ae71acdb5f5 from=translated src=- shape=b9369acb vocab=b06d93e1
-/
lemma radialY_nonneg (d : EulerData) : 0 ≤ radialY d := Real.sqrt_nonneg _

def lopDiag (p : I3 → ℝ) : I3 → ℝ :=
  ![(p 1 - p 2) ^ 2, (p 2 - p 0) ^ 2, (p 0 - p 1) ^ 2]

/--
@isnad1 id=eq.0h2v.s9.18896a9fa787 from=translated src=- shape=56ab2f47 vocab=3d3efde2
-/
lemma lop'_conjugate_so3 (P : Mat3) (U : SO3) :
    lop' ((U : Mat3)ᵀ * P * U) =
      (U : Mat3)ᵀ * lop' P * U := by
  let T : Mat3 := U
  have hTT : T * Tᵀ = 1 := so3_mul_transpose U
  have hTtT : Tᵀ * T = 1 := so3_transpose_mul U
  have hsq : (Tᵀ * P * T) * (Tᵀ * P * T) = Tᵀ * (P * P) * T := by
    calc
      (Tᵀ * P * T) * (Tᵀ * P * T) =
          Tᵀ * P * (T * Tᵀ) * P * T := by noncomm_ring
      _ = Tᵀ * (P * P) * T := by rw [hTT]; simp; noncomm_ring
  have htrace : (Tᵀ * (P * P) * T).trace = (P * P).trace := by
    calc
      (Tᵀ * (P * P) * T).trace = (T * Tᵀ * (P * P)).trace :=
        Matrix.trace_mul_cycle Tᵀ (P * P) T
      _ = (P * P).trace := by rw [hTT]; simp
  have hcof : cofactor3 (Tᵀ * P * T) = Tᵀ * cofactor3 P * T := by
    exact cofactor3_so3_conjugate U P
  rw [lop', lop', hsq, htrace, hcof]
  have hone : Tᵀ * (1 : Mat3) * T = 1 := by
    rw [Matrix.mul_one, hTtT]
  calc
    (P * P).trace • (1 : Mat3) - Tᵀ * (P * P) * T -
          (2 : ℝ) • (Tᵀ * cofactor3 P * T) =
        Tᵀ * ((P * P).trace • (1 : Mat3)) * T -
          Tᵀ * (P * P) * T -
          Tᵀ * ((2 : ℝ) • cofactor3 P) * T := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul, hone]
    _ = Tᵀ * ((P * P).trace • (1 : Mat3) - P * P -
          (2 : ℝ) • cofactor3 P) * T := by noncomm_ring

/--
@isnad1 id=lt.1h1v.s4.500f15808c82 from=translated src=- shape=c87724ab vocab=da666fe8
-/
lemma normSq3_pos {v : Vec3} (hv : v ≠ 0) :
    0 < S3xS3.Trivial.normSq3 v := by
  have hnonneg : 0 ≤ S3xS3.Trivial.normSq3 v := by
    simp [S3xS3.Trivial.normSq3]
    positivity
  apply lt_of_le_of_ne hnonneg
  intro hz
  apply hv
  funext i
  fin_cases i <;>
    simp [S3xS3.Trivial.normSq3, Fin.sum_univ_succ] at hz ⊢ <;> nlinarith

def kopDiag (h : I3 → ℝ) : I3 → ℝ :=
  ![h 1 * h 2 - 2 * h 1 - 2 * h 2 + 2 * h 0,
    h 0 * h 2 - 2 * h 0 - 2 * h 2 + 2 * h 1,
    h 0 * h 1 - 2 * h 0 - 2 * h 1 + 2 * h 2]

def basis3 (i : I3) : Vec3 := fun j ↦ if j = i then 1 else 0

/--
@isnad1 id=ne.0h1v.s4.a88048607906 from=translated src=- shape=a311c14d vocab=e2d4bee2
-/
lemma basis3_ne_zero (i : I3) : basis3 i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basis3] at hi

/--
@isnad1 id=lt.5h3v.s7.0a07c10daea1 from=translated src=- shape=9f3baff2 vocab=7435bc9b
-/
lemma threshold_four_two_others {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hat : a ≤ t) (hbt : b ≤ t)
    (ht : 4 ≤ t) :
    0 < a * b - 2 * a - 2 * b + 2 * t := by
  by_cases hab : a ≤ b
  · exact S3xS3.Trivial.threshold_four_scalar ha hab hbt ht
  · have hba : b ≤ a := le_of_not_ge hab
    have h := S3xS3.Trivial.threshold_four_scalar hb hba hat ht
    nlinarith

/--
@isnad1 id=eq.1h3v.s6.c2f880dc0274 from=translated src=- shape=506cd657 vocab=149dc9ff
-/
lemma scalarMatrix_inv_offdiag (p : ℝ) {i j : I3} (hij : i ≠ j) :
    (p • (1 : Mat3))⁻¹ i j = 0 := by
  have heq : p • (1 : Mat3) = Matrix.diagonal (fun _ : I3 ↦ p) := by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp
    · simp [Matrix.diagonal, hrs]
  rw [heq, Matrix.inv_diagonal]
  simp [Matrix.diagonal, hij]

/--
@isnad1 id=eq.2h3v.s7.cb8410a9269f from=translated src=- shape=4cb2fca4 vocab=4b001ffc
-/
lemma scalarP_diagonalM_offQ0 (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m) :
    m 0 * (m 1 ^ 2 + m 2 ^ 2) * d.Q 1 2 = 0 := by
  have hij := congrFun (congrFun d.gradP 1) 2
  rw [hP, hM] at hij
  have hrhs : (d.kappa • (p • (1 : Mat3))⁻¹) 1 2 = 0 := by
    rw [real_smul_apply, scalarMatrix_inv_offdiag p (by decide)]
    ring
  rw [hrhs] at hij
  have hsym : d.Q 2 1 = d.Q 1 2 := by
    have hq := congrFun (congrFun d.Q_pos.isHermitian.eq 1) 2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hq
  simp [residual, dcof, cofactor3, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ] at hij
  rw [hsym] at hij
  ring_nf at hij ⊢
  linarith

/--
@isnad1 id=eq.2h3v.s7.f29a2c2de5a7 from=translated src=- shape=4cb2fca4 vocab=4b001ffc
-/
lemma scalarP_diagonalM_offQ1 (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m) :
    m 1 * (m 0 ^ 2 + m 2 ^ 2) * d.Q 0 2 = 0 := by
  have hij := congrFun (congrFun d.gradP 0) 2
  rw [hP, hM] at hij
  have hrhs : (d.kappa • (p • (1 : Mat3))⁻¹) 0 2 = 0 := by
    rw [real_smul_apply, scalarMatrix_inv_offdiag p (by decide)]
    ring
  rw [hrhs] at hij
  have hsym : d.Q 2 0 = d.Q 0 2 := by
    have hq := congrFun (congrFun d.Q_pos.isHermitian.eq 0) 2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hq
  simp [residual, dcof, cofactor3, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ] at hij
  rw [hsym] at hij
  ring_nf at hij ⊢
  linarith

/--
@isnad1 id=eq.2h3v.s7.d3313bb7e416 from=translated src=- shape=4cb2fca4 vocab=4b001ffc
-/
lemma scalarP_diagonalM_offQ2 (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m) :
    m 2 * (m 0 ^ 2 + m 1 ^ 2) * d.Q 0 1 = 0 := by
  have hij := congrFun (congrFun d.gradP 0) 1
  rw [hP, hM] at hij
  have hrhs : (d.kappa • (p • (1 : Mat3))⁻¹) 0 1 = 0 := by
    rw [real_smul_apply, scalarMatrix_inv_offdiag p (by decide)]
    ring
  rw [hrhs] at hij
  have hsym : d.Q 1 0 = d.Q 0 1 := by
    have hq := congrFun (congrFun d.Q_pos.isHermitian.eq 0) 1
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hq
  simp [residual, dcof, cofactor3, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ] at hij
  rw [hsym] at hij
  ring_nf at hij ⊢
  linarith

/--
@isnad1 id=eq.3h3v.s6.ceca8aec76d4 from=translated src=- shape=388691ac vocab=58b1427c
-/
lemma scalarP_diagonalM_Q_diagonal (d : EulerData) {p : ℝ} {m : I3 → ℝ}
    (hP : d.P = p • (1 : Mat3)) (hM : d.M = Matrix.diagonal m)
    (hm : ∀ i, m i ≠ 0) :
    d.Q = Matrix.diagonal (fun i ↦ d.Q i i) := by
  have h0eq := scalarP_diagonalM_offQ0 d hP hM
  have h1eq := scalarP_diagonalM_offQ1 d hP hM
  have h2eq := scalarP_diagonalM_offQ2 d hP hM
  have hs0 : 0 < m 1 ^ 2 + m 2 ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (hm 1), sq_pos_of_ne_zero (hm 2)]
  have hs1 : 0 < m 0 ^ 2 + m 2 ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (hm 0), sq_pos_of_ne_zero (hm 2)]
  have hs2 : 0 < m 0 ^ 2 + m 1 ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (hm 0), sq_pos_of_ne_zero (hm 1)]
  have hy0 : d.Q 1 2 = 0 := by
    rcases mul_eq_zero.mp h0eq with hcoef | hy
    · rcases mul_eq_zero.mp hcoef with hm0 | hsum
      · exact (hm 0 hm0).elim
      · exact (ne_of_gt hs0 hsum).elim
    · exact hy
  have hy1 : d.Q 0 2 = 0 := by
    rcases mul_eq_zero.mp h1eq with hcoef | hy
    · rcases mul_eq_zero.mp hcoef with hm1 | hsum
      · exact (hm 1 hm1).elim
      · exact (ne_of_gt hs1 hsum).elim
    · exact hy
  have hy2 : d.Q 0 1 = 0 := by
    rcases mul_eq_zero.mp h2eq with hcoef | hy
    · rcases mul_eq_zero.mp hcoef with hm2 | hsum
      · exact (hm 2 hm2).elim
      · exact (ne_of_gt hs2 hsum).elim
    · exact hy
  have hQt : d.Qᵀ = d.Q := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using d.Q_pos.isHermitian.eq
  have hy0' : d.Q 2 1 = 0 := by
    have := congrFun (congrFun hQt 1) 2
    simpa [hy0] using this
  have hy1' : d.Q 2 0 = 0 := by
    have := congrFun (congrFun hQt 0) 2
    simpa [hy1] using this
  have hy2' : d.Q 1 0 = 0 := by
    have := congrFun (congrFun hQt 0) 1
    simpa [hy2] using this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hy0, hy1, hy2, hy0', hy1', hy2']

end S3xS3.Trivial.Euler
