import Tengoku.Nlalib.NLAlib.Matrix.Functions.LyapunovADIFactors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Fixed positive-shift convergence of the actual low-rank ADI process -/
noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology
namespace NLAlib
variable {n s : Type*} [Fintype n] [Fintype s] [DecidableEq n]

/-- Positive shifts of a Hurwitz matrix make every actual ADI solve admissible.-/
theorem IsHurwitz.lyapunovADI_admissible {A : Matrix n n ℂ} (hA : IsHurwitz A)
    (p : ℕ → ℝ) (hp : ∀ j, 0 < p j) (j : ℕ) :
    IsUnit (A - (p j : ℂ) • 1).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (hA.isUnit_sub_pos_smul_one (p j) (hp j))

/-- The spectral error estimate is obtained from the exact matrix error.-/
theorem specNorm_sub_lyapunovADI_le (A X : Matrix n n ℂ) (B : Matrix n s ℂ)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : ℂ) • 1).det)
    (hX : A * X + X * Aᴴ + B * Bᴴ = 0) (j : ℕ) :
    specNorm (X - (lyapunovADI A B p j).2) ≤
      specNorm (lyapunovADIPropagator A p j) ^ 2 * specNorm X := by
  rw [sub_lyapunovADI_snd A X B p hP hX]
  calc
    _ ≤ specNorm (lyapunovADIPropagator A p j * X) * specNorm (lyapunovADIPropagator A p j)ᴴ := specNorm_mul_le _ _
    _ ≤ (specNorm (lyapunovADIPropagator A p j) * specNorm X) * specNorm (lyapunovADIPropagator A p j) := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- The Frobenius error obeys the same spectral propagator coefficient.-/
theorem frobNorm_sub_lyapunovADI_le (A X : Matrix n n ℂ) (B : Matrix n s ℂ)
    (p : ℕ → ℝ) (hP : ∀ j, IsUnit (A - (p j : ℂ) • 1).det)
    (hX : A * X + X * Aᴴ + B * Bᴴ = 0) (j : ℕ) :
    frobNorm (X - (lyapunovADI A B p j).2) ≤
      specNorm (lyapunovADIPropagator A p j) ^ 2 * frobNorm X := by
  rw [sub_lyapunovADI_snd A X B p hP hX]
  calc
    _ ≤ frobNorm (lyapunovADIPropagator A p j * X) * specNorm (lyapunovADIPropagator A p j)ᴴ := frobNorm_mul_le_frobNorm_mul_specNorm _ _
    _ ≤ (specNorm (lyapunovADIPropagator A p j) * frobNorm X) * specNorm (lyapunovADIPropagator A p j) := by
      rw [specNorm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (frobNorm_mul_le_specNorm_mul_frobNorm _ _) (specNorm_nonneg _)
    _ = _ := by ring

/-- A fixed shift gives the actual powers of its Cayley matrix.-/
theorem lyapunovADIPropagator_const (A : Matrix n n ℂ) (p : ℝ) (j : ℕ) :
    lyapunovADIPropagator A (fun _ => p) j = cayleyTransform A p ^ j := by
  induction j with
  | zero => rfl
  | succ j hj => rw [lyapunovADIPropagator, hj, pow_succ']

end NLAlib
