import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unit quaternions and the rotation homomorphism to SO(3)

This file defines the group `Submission.SpinOne` of unit quaternions (the unit sphere in
`ℍ = Quaternion ℝ`, which Mathlib already equips with a topological group structure), the
explicit rotation matrix `Submission.rotMatrix q` of the conjugation action
`v ↦ q * v * star q` on pure-imaginary quaternions, and the resulting group homomorphism

* `Submission.spinToSO : SpinOne →* Matrix.specialOrthogonalGroup (Fin 3) ℝ`.

Main algebraic facts:

* `Submission.conj_fromIm` : `q * fromIm v * star q = fromIm (rotMatrix q *ᵥ v)`;
* `Submission.rotMatrix_mul`, `rotMatrix_star`, `det_rotMatrix`;
* `Submission.rotMatrix_mem_specialOrthogonalGroup`;
* `Submission.continuous_spinToSO`;
* `Submission.spinToSO_mem_ker_iff` : the kernel of `spinToSO` is `{1, -1}`.
-/

noncomputable section

open Quaternion Metric
open scoped Matrix

namespace Submission

/-- The group of unit quaternions (`S³` as a topological group).-/
abbrev SpinOne : Type := Metric.sphere (0 : ℍ) 1

/--
@isnad1 id=eq.1h1v.s8.0509239c5aa0 from=translated src=- shape=92a806a8 vocab=a6d8ce15
-/
theorem normSq_of_mem_sphere {q : ℍ} (hq : q ∈ Metric.sphere (0 : ℍ) 1) :
    normSq q = 1 := by
  rw [mem_sphere_zero_iff_norm] at hq
  rw [Quaternion.normSq_eq_norm_mul_self, hq, one_mul]

/--
@isnad1 id=mem.1h1v.s8.773d9ddddb5b from=translated src=- shape=9fffedb3 vocab=a6d8ce15
-/
theorem mem_sphere_of_normSq {q : ℍ} (hq : normSq q = 1) :
    q ∈ Metric.sphere (0 : ℍ) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h : ‖q‖ * ‖q‖ = 1 := by rw [← Quaternion.normSq_eq_norm_mul_self, hq]
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · nlinarith [norm_nonneg q]

/-- The 3×3 rotation matrix of the conjugation `v ↦ q * v * star q` on
pure-imaginary quaternions, in coordinates `(imI, imJ, imK)`.-/
def rotMatrix (q : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
    2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
    2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

/-- Realize a vector `v : Fin 3 → ℝ` as a pure-imaginary quaternion.-/
def fromIm (v : Fin 3 → ℝ) : ℍ := ⟨0, v 0, v 1, v 2⟩

/--
@isnad1 id=eq.0h1v.s5.c898eac238cb from=translated src=- shape=bafbdab0 vocab=b5069e32
-/
@[simp] theorem fromIm_re (v : Fin 3 → ℝ) : (fromIm v).re = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.af2637907743 from=translated src=- shape=29d78908 vocab=5787fd44
-/
@[simp] theorem fromIm_imI (v : Fin 3 → ℝ) : (fromIm v).imI = v 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.54d880bcbc89 from=translated src=- shape=29d78908 vocab=5b41b562
-/
@[simp] theorem fromIm_imJ (v : Fin 3 → ℝ) : (fromIm v).imJ = v 1 := rfl
/--
@isnad1 id=eq.0h1v.s5.c63cc93f0394 from=translated src=- shape=29d78908 vocab=b2e9cbce
-/
@[simp] theorem fromIm_imK (v : Fin 3 → ℝ) : (fromIm v).imK = v 2 := rfl

/--
@isnad1 id=eq.0h2v.s7.037ec2092f08 from=translated src=- shape=86123ef7 vocab=352f3b93
-/
theorem rotMatrix_mul (p q : ℍ) : rotMatrix (p * q) = rotMatrix p * rotMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

/--
@isnad1 id=eq.0h1v.s5.d81ca6cc23d6 from=translated src=- shape=9e96c186 vocab=3967f86b
-/
theorem rotMatrix_star (q : ℍ) : rotMatrix (star q) = (rotMatrix q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, Matrix.transpose_apply] <;> ring

/--
@isnad1 id=eq.0h1v.s7.16c6b47d437b from=translated src=- shape=cca3b58d vocab=1729fa40
-/
theorem rotMatrix_coe (r : ℝ) : rotMatrix (r : ℍ) = r ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, Matrix.smul_apply, Matrix.one_apply] <;> ring

/--
@isnad1 id=eq.0h0v.s6.0360106faf34 from=translated src=- shape=065272bc vocab=bcc22d59
-/
theorem rotMatrix_one : rotMatrix (1 : ℍ) = 1 := by
  rw [← Quaternion.coe_one, rotMatrix_coe]
  norm_num

/--
@isnad1 id=eq.0h1v.s6.367d464d4bb9 from=translated src=- shape=628b9988 vocab=04c0945e
-/
theorem rotMatrix_neg (q : ℍ) : rotMatrix (-q) = rotMatrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMatrix] <;> ring

/--
@isnad1 id=eq.0h1v.s8.2bf95cf9059d from=translated src=- shape=668f4694 vocab=72add028
-/
theorem det_rotMatrix (q : ℍ) : (rotMatrix q).det = normSq q ^ 3 := by
  rw [Matrix.det_fin_three, Quaternion.normSq_def']
  simp [rotMatrix]
  ring

/--
@isnad1 id=eq.1h1v.s8.f4dff131552e from=translated src=- shape=892eaa08 vocab=2138e3c4
-/
theorem rotMatrix_mul_transpose {q : ℍ} (hq : normSq q = 1) :
    rotMatrix q * (rotMatrix q)ᵀ = 1 := by
  rw [← rotMatrix_star, ← rotMatrix_mul, Quaternion.self_mul_star, hq, rotMatrix_coe]
  norm_num

/--
@isnad1 id=mem.1h1v.s9.41915feeb6a8 from=translated src=- shape=61c92ba9 vocab=9ef41bff
-/
theorem rotMatrix_mem_specialOrthogonalGroup {q : ℍ} (hq : normSq q = 1) :
    rotMatrix q ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    exact rotMatrix_mul_transpose hq
  · rw [det_rotMatrix, hq, one_pow]

/-- The double-cover homomorphism from the unit quaternions to `SO(3)`.-/
def spinToSO : SpinOne →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun q := ⟨rotMatrix (q : ℍ), rotMatrix_mem_specialOrthogonalGroup (normSq_of_mem_sphere q.2)⟩
  map_one' := Subtype.ext <| by
    show rotMatrix ((1 : SpinOne) : ℍ) = 1
    rw [show ((1 : SpinOne) : ℍ) = 1 from rfl, rotMatrix_one]
  map_mul' p q := Subtype.ext <| by
    show rotMatrix ((p * q : SpinOne) : ℍ) = _
    rw [show ((p * q : SpinOne) : ℍ) = (p : ℍ) * (q : ℍ) from rfl, rotMatrix_mul]
    rfl

/--
@isnad1 id=eq.0h1v.s11.0f2cf1322619 from=translated src=- shape=e6b822ab vocab=fef57055
-/
@[simp] theorem spinToSO_apply_coe (q : SpinOne) :
    (spinToSO q : Matrix (Fin 3) (Fin 3) ℝ) = rotMatrix (q : ℍ) := rfl

/--
@isnad1 id=continuo.0h0v.s6.dc48325ad533 from=translated src=- shape=aabdcd42 vocab=c5c38c3c
-/
theorem continuous_rotMatrix : Continuous rotMatrix := by
  have a : Continuous fun q : ℍ => q.re := Quaternion.continuous_re
  have b : Continuous fun q : ℍ => q.imI := Quaternion.continuous_imI
  have c : Continuous fun q : ℍ => q.imJ := Quaternion.continuous_imJ
  have d : Continuous fun q : ℍ => q.imK := Quaternion.continuous_imK
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotMatrix, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  · exact (((a.pow 2).add (b.pow 2)).sub (c.pow 2)).sub (d.pow 2)
  · exact continuous_const.mul ((b.mul c).sub (a.mul d))
  · exact continuous_const.mul ((b.mul d).add (a.mul c))
  · exact continuous_const.mul ((b.mul c).add (a.mul d))
  · exact (((a.pow 2).sub (b.pow 2)).add (c.pow 2)).sub (d.pow 2)
  · exact continuous_const.mul ((c.mul d).sub (a.mul b))
  · exact continuous_const.mul ((b.mul d).sub (a.mul c))
  · exact continuous_const.mul ((c.mul d).add (a.mul b))
  · exact (((a.pow 2).sub (b.pow 2)).sub (c.pow 2)).add (d.pow 2)

/--
@isnad1 id=continuo.0h0v.s11.2b9121a1665a from=translated src=- shape=ab40005b vocab=dab9cfdd
-/
theorem continuous_spinToSO : Continuous spinToSO := by
  apply Continuous.subtype_mk
  exact continuous_rotMatrix.comp continuous_subtype_val

/-- `-1` is a unit quaternion.
@isnad1 id=eq.0h0v.s11.498a40430d2b from=translated src=- shape=3a48a755 vocab=d1a1f7ec
-/
theorem spinToSO_neg_one : spinToSO (-1 : SpinOne) = 1 := by
  apply Subtype.ext
  show rotMatrix ((-1 : SpinOne) : ℍ) = 1
  rw [show ((-1 : SpinOne) : ℍ) = -(1 : ℍ) from rfl, rotMatrix_neg, rotMatrix_one]

/--
@isnad1 id=iff.1h1v.s9.c3344934ab33 from=translated src=- shape=583eeca9 vocab=30de5ea2
-/
theorem rotMatrix_eq_one_iff {q : ℍ} (hq : normSq q = 1) :
    rotMatrix q = 1 ↔ q = 1 ∨ q = -1 := by
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h 0) 0
    have h11 := congr_fun (congr_fun h 1) 1
    simp [rotMatrix, Matrix.one_apply] at h00 h11
    rw [Quaternion.normSq_def'] at hq
    have hJK : q.imJ ^ 2 + q.imK ^ 2 = 0 := by linarith
    have hIK : q.imI ^ 2 + q.imK ^ 2 = 0 := by linarith
    have hJ : q.imJ = 0 := by nlinarith [sq_nonneg q.imJ, sq_nonneg q.imK]
    have hK : q.imK = 0 := by nlinarith [sq_nonneg q.imJ, sq_nonneg q.imK]
    have hI : q.imI = 0 := by nlinarith [sq_nonneg q.imI, sq_nonneg q.imK]
    have hre : q.re ^ 2 = 1 := by nlinarith
    rcases sq_eq_one_iff.mp hre with h1 | h1
    · left; ext <;> simp [h1, hI, hJ, hK]
    · right; ext <;> simp [h1, hI, hJ, hK]
  · rintro (rfl | rfl)
    · exact rotMatrix_one
    · rw [rotMatrix_neg, rotMatrix_one]

/--
@isnad1 id=iff.0h1v.s9.5437e33e22ee from=translated src=- shape=9d6b6883 vocab=56d79816
-/
theorem spinToSO_mem_ker_iff (q : SpinOne) :
    q ∈ spinToSO.ker ↔ q = 1 ∨ q = -1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : rotMatrix (q : ℍ) = 1 := congr_arg Subtype.val h
    rcases (rotMatrix_eq_one_iff (normSq_of_mem_sphere q.2)).mp h' with h1 | h1
    · left; exact Subtype.ext h1
    · right
      apply Subtype.ext
      rw [h1, show ((-1 : SpinOne) : ℍ) = -(1 : ℍ) from rfl]
  · rintro (rfl | rfl)
    · exact map_one spinToSO
    · exact spinToSO_neg_one

end Submission
