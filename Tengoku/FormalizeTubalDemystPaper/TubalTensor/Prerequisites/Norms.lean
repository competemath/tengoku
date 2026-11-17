import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Prerequisites.SVD
import Tengoku.Seed.Data.Complex.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Prerequisites/Norms.lean
  Squared Frobenius norm for complex matrices: definition and basic properties.

  The key results are:
  - `frobNormSq`: ∑ᵢⱼ |Aᵢⱼ|²
  - `frobNormSq_nonneg`: nonnegativity
  - `frobNormSq_eq_re_trace`: equals re(trace(Aᴴ * A))
  - `frobNormSq_unitary_mul_left` / `frobNormSq_unitary_mul_right`: unitary invariance
-/

namespace TubalTensor

open Matrix Complex BigOperators

/-! ## Frobenius norm squared -/

/-- Squared Frobenius norm for a complex matrix: ∑ᵢⱼ |Aᵢⱼ|².-/
noncomputable def frobNormSq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, Complex.normSq (A i j)

theorem frobNormSq_nonneg {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) :
    0 ≤ frobNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-! ## Trace characterization -/

/-- Frobenius norm squared equals re(trace(Aᴴ * A)).-/
theorem frobNormSq_eq_re_trace {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℂ) :
    frobNormSq A = (Matrix.trace (Aᴴ * A)).re := by
  unfold frobNormSq
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have key : ∀ z : ℂ, Complex.normSq z = (star z * z).re := by
    intro z; simp [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp_rw [key]
  simp only [Complex.re_sum]
  exact Finset.sum_comm

/-! ## Unitary invariance -/

/-- Left multiplication by a unitary matrix preserves Frobenius norm squared.-/
theorem frobNormSq_unitary_mul_left {m p : ℕ}
    (U : Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin m) (Fin p) ℂ)
    (hU : IsUnitary U) :
    frobNormSq (U * X) = frobNormSq X := by
  rw [frobNormSq_eq_re_trace, frobNormSq_eq_re_trace]
  congr 1
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U X,
    hU.conjTranspose_mul_self, Matrix.one_mul]

/-- Right multiplication by a unitary matrix preserves Frobenius norm squared.-/
theorem frobNormSq_unitary_mul_right {m p : ℕ}
    (X : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin p) ℂ)
    (hV : IsUnitary V) :
    frobNormSq (X * V) = frobNormSq X := by
  rw [frobNormSq_eq_re_trace, frobNormSq_eq_re_trace]
  congr 1
  rw [conjTranspose_mul, Matrix.mul_assoc Vᴴ Xᴴ (X * V),
    ← Matrix.mul_assoc Xᴴ X V,
    Matrix.trace_mul_cycle' Vᴴ (Xᴴ * X) V,
    ← Matrix.mul_assoc V Vᴴ (Xᴴ * X),
    hV.mul_conjTranspose_self, Matrix.one_mul]

end TubalTensor
