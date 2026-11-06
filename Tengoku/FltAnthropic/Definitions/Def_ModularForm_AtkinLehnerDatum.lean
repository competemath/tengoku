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

lemma q_pos [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

def mat : Matrix (Fin 2) (Fin 2) ℤ := !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)]

@[simp] lemma det_mat : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout

def sqUnit : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b, W.b * (W.a + 1);
     (q : ℤ) * (W.R : ℤ) * (W.a + 1), (W.R : ℤ) * W.b + (q : ℤ)]

@[simp] lemma det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout

def sqUnitSL : SL(2, ℤ) := ⟨W.sqUnit, W.det_sqUnit⟩

@[simp] lemma sqUnitSL_coe : (W.sqUnitSL : Matrix (Fin 2) (Fin 2) ℤ) = W.sqUnit := rfl

def alGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℝ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

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
