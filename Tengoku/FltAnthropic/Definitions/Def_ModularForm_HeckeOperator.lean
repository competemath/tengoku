import Tengoku.Seed.NumberTheory.ModularForms.SlashActions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularForm

def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

/--
@isnad1 id=eq.1h3v.s8.0dfe2fa98792 from=translated src=- shape=f526e8a0 vocab=d9d34ce2
-/
@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] := rfl

def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

/--
@isnad1 id=eq.1h2v.s8.17d7b9cb8f26 from=translated src=- shape=84ea79a3 vocab=a14f53f5
-/
@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

/--
@isnad1 id=eq.1h1v.s8.52d82096f99f from=translated src=- shape=c4fd969a vocab=f17fd92e
-/
@[simp] theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hp]

/--
@isnad1 id=eq.0h1v.s6.c7c85df065f6 from=translated src=- shape=791023cf vocab=c5a86332
-/
@[simp] theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

/--
@isnad1 id=eq.0h0v.s6.e3304e088405 from=translated src=- shape=59a246a7 vocab=ecdc1277
-/
@[simp] theorem heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by simp [heckeDiagMatrix]

def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

/--
@isnad1 id=eq.0h2v.s5.94ded41341ef from=translated src=- shape=774e60b7 vocab=31e90975
-/
@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

/--
@isnad1 id=eq.0h2v.s4.a7791f84ff24 from=translated src=- shape=1c3f5016 vocab=e5a4ae70
-/
@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

/--
@isnad1 id=eq.0h2v.s5.b20050cf18bf from=translated src=- shape=efc8b39d vocab=31e90975
-/
@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

/--
@isnad1 id=eq.0h2v.s5.36d65e8ade86 from=translated src=- shape=efc8b39d vocab=e5a4ae70
-/
@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

end ModularForm

end
