import Tengoku.Seed.NumberTheory.ModularForms.SlashActions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularForm

def upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, d]
    (by rwa [Matrix.det_fin_two_of, mul_zero, sub_zero])

@[simp] theorem val_upperTriangularGL (a b d : ℝ) (had : a * d ≠ 0) :
    ((upperTriangularGL a b d had : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; 0, d] := rfl

def heckeMatrix (p j : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL 1 j p (by rw [one_mul]; exact_mod_cast hp)

def heckeDiagMatrix (p : ℕ) : GL (Fin 2) ℝ :=
  if hp : p = 0 then 1 else upperTriangularGL p 0 1 (by rw [mul_one]; exact_mod_cast hp)

@[simp] theorem val_heckeMatrix {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)] := by
  simp [heckeMatrix, hp]

@[simp] theorem val_heckeDiagMatrix {p : ℕ} (hp : p ≠ 0) :
    ((heckeDiagMatrix p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
  simp [heckeDiagMatrix, hp]

@[simp] theorem heckeMatrix_zero (j : ℕ) : heckeMatrix 0 j = 1 := by simp [heckeMatrix]

@[simp] theorem heckeDiagMatrix_zero : heckeDiagMatrix 0 = 1 := by simp [heckeDiagMatrix]

def heckeU (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  ∑ j ∈ Finset.range p, f ∣[k] heckeMatrix p j

def heckeT (k : ℤ) (p : ℕ) (f : UpperHalfPlane → ℂ) : UpperHalfPlane → ℂ :=
  heckeU k p f + f ∣[k] heckeDiagMatrix p

@[simp] theorem heckeU_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeU k 0 f = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero_left (k : ℤ) (f : UpperHalfPlane → ℂ) : heckeT k 0 f = f := by
  simp [heckeT]

@[simp] theorem heckeU_zero (k : ℤ) (p : ℕ) : heckeU k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeU]

@[simp] theorem heckeT_zero (k : ℤ) (p : ℕ) : heckeT k p (0 : UpperHalfPlane → ℂ) = 0 := by
  simp [heckeT]

def coeffHeckeT (k : ℤ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

def coeffHeckeU (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p)

end ModularForm

end
