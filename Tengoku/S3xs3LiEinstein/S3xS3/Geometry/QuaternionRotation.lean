import Tengoku.S3xs3LiEinstein.S3xS3.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix BigOperators

namespace S3xS3.Geometry

open Quaternion

noncomputable section

/-- The unit quaternions, used as the concrete group model of `SU(2)`.-/
abbrev QuaternionSU2 := unitary ℍ

/-- A quaternion of norm-square one is a unit quaternion.-/
noncomputable def quaternionSU2OfNormSqOne (q : ℍ) (hq : Quaternion.normSq q = 1) :
    QuaternionSU2 :=
  ⟨q, by
    constructor
    · rw [Quaternion.star_mul_self, hq]
      norm_num
    · rw [Quaternion.self_mul_star, hq]
      norm_num⟩

lemma quaternionSU2_normSq (q : QuaternionSU2) :
    Quaternion.normSq (q : ℍ) = 1 := by
  have h := q.property.2
  rw [Quaternion.self_mul_star] at h
  have hre := congrArg (fun x : ℍ ↦ x.re) h
  simpa using hre

/-- Euler--Rodrigues matrix of quaternion conjugation on the imaginary
quaternions.  This homogeneous formula is useful before imposing unit norm.-/
def quaternionRotationMatrix (q : ℍ) : Mat3 :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
     2 * (q.imI * q.imJ + q.re * q.imK),
      q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
     2 * (q.imI * q.imK - q.re * q.imJ),
      2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

@[simp]
lemma quaternionRotationMatrix_one :
    quaternionRotationMatrix (1 : ℍ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotationMatrix]

lemma quaternionRotationMatrix_mul (q r : ℍ) :
    quaternionRotationMatrix (q * r) =
      quaternionRotationMatrix q * quaternionRotationMatrix r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring

lemma quaternionRotationMatrix_mul_transpose (q : ℍ) :
    quaternionRotationMatrix q * (quaternionRotationMatrix q)ᵀ =
      (Quaternion.normSq q) ^ 2 • (1 : Mat3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRotationMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
      Quaternion.normSq_def'] <;>
    ring

lemma quaternionRotationMatrix_det (q : ℍ) :
    (quaternionRotationMatrix q).det = (Quaternion.normSq q) ^ 3 := by
  simp [quaternionRotationMatrix, Matrix.det_fin_three,
    Quaternion.normSq_def']
  ring

/-- The adjoint double-cover homomorphism from unit quaternions to `SO(3)`.-/
def quaternionAdjoint : QuaternionSU2 →* SO3 where
  toFun q := ⟨quaternionRotationMatrix q, by
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    constructor
    · rw [Matrix.mem_orthogonalGroup_iff,
        quaternionRotationMatrix_mul_transpose, quaternionSU2_normSq]
      simp
    · rw [quaternionRotationMatrix_det, quaternionSU2_normSq]
      norm_num⟩
  map_one' := by
    apply Subtype.ext
    exact quaternionRotationMatrix_one
  map_mul' q r := by
    apply Subtype.ext
    exact quaternionRotationMatrix_mul q r

@[simp]
lemma quaternionAdjoint_coe (q : QuaternionSU2) :
    ((quaternionAdjoint q : SO3) : Mat3) = quaternionRotationMatrix q := rfl

/-! ## Algebraic surjectivity certificate -/

abbrev I4 := Fin 4
abbrev Mat4 := Matrix I4 I4 ℝ

/-- The rank-one quaternion Gram matrix associated with a rotation matrix.
For a rotation represented by `q = a + bi + cj + dk`, this is exactly
`![a,b,c,d] * ![a,b,c,d]ᵀ`.-/
def quaternionGram (R : Mat3) : Mat4 :=
  !![(1 + R 0 0 + R 1 1 + R 2 2) / 4,
      (R 2 1 - R 1 2) / 4,
      (R 0 2 - R 2 0) / 4,
      (R 1 0 - R 0 1) / 4;
     (R 2 1 - R 1 2) / 4,
      (1 + R 0 0 - R 1 1 - R 2 2) / 4,
      (R 0 1 + R 1 0) / 4,
      (R 0 2 + R 2 0) / 4;
     (R 0 2 - R 2 0) / 4,
      (R 0 1 + R 1 0) / 4,
      (1 - R 0 0 + R 1 1 - R 2 2) / 4,
      (R 1 2 + R 2 1) / 4;
     (R 1 0 - R 0 1) / 4,
      (R 0 2 + R 2 0) / 4,
      (R 1 2 + R 2 1) / 4,
      (1 - R 0 0 - R 1 1 + R 2 2) / 4]

end

end S3xS3.Geometry
