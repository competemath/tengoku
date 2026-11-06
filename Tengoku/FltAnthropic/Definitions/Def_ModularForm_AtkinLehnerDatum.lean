import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace ModularForm

variable (M q : ℕ)

structure AtkinLehnerDatum : Type where

  R : ℕ

  hM : M = q * R

  a : ℤ

  b : ℤ

  bezout : (q : ℤ) * a - (R : ℤ) * b = 1

namespace AtkinLehnerDatum

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

include W in

/--
@isnad1 id=lt.0h3v.s4.195819f01c1d from=translated src=- shape=480a14fa vocab=47a9b35e
-/
lemma q_pos [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

def mat : Matrix (Fin 2) (Fin 2) ℤ := !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)]

/--
@isnad1 id=eq.0h3v.s5.688ff63a5de0 from=translated src=- shape=94c68e3f vocab=b365ca4e
-/
@[simp] lemma det_mat : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout

def sqUnit : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b, W.b * (W.a + 1);
     (q : ℤ) * (W.R : ℤ) * (W.a + 1), (W.R : ℤ) * W.b + (q : ℤ)]

/--
@isnad1 id=eq.0h3v.s5.2600b3d7f4e2 from=translated src=- shape=aa0bce4b vocab=bd82a9f0
-/
@[simp] lemma det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout

def sqUnitSL : SL(2, ℤ) := ⟨W.sqUnit, W.det_sqUnit⟩

/--
@isnad1 id=eq.0h3v.s6.adb51d4193c8 from=translated src=- shape=8c772932 vocab=66e4ee71
-/
@[simp] lemma sqUnitSL_coe : (W.sqUnitSL : Matrix (Fin 2) (Fin 2) ℤ) = W.sqUnit := rfl

def alGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℝ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

/--
@isnad1 id=eq.0h3v.s7.8179fe407a16 from=translated src=- shape=3a03a649 vocab=2c924023
-/
@[simp] lemma alGL_coe [NeZero M] :
    (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) = (W.mat).map (algebraMap ℤ ℝ) := rfl

def alGLQ [NeZero M] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℚ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

end AtkinLehnerDatum

def alSlash {M q : ℕ} (W : AtkinLehnerDatum M q) (k : ℤ) [NeZero M] (f : ℍ → ℂ) : ℍ → ℂ :=
  f ∣[k] W.alGL

end ModularForm

end
