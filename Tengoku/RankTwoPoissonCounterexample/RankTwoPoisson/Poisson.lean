import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Definitions
import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.SourceCoordinates
import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact Poisson identities and global preservation

The six large identities are discharged as exact polynomial identities over
`ℚ`.  The generator identities are then promoted to all multivariate
polynomials using `MvPolynomial.induction_on` and the biderivation laws.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson

noncomputable section

open MvPolynomial

/-- The canonical bracket is skew-symmetric.-/
theorem bracket_skew (f g : P) : bracket f g = -bracket g f := by
  simp [bracket] <;> ring

@[simp] theorem bracket_self (f : P) : bracket f f = 0 := by
  simp [bracket] <;> ring

@[simp] theorem bracket_C_left (c : ℚ) (f : P) : bracket (C c) f = 0 := by
  simp [bracket, polyDeriv]

@[simp] theorem bracket_C_right (f : P) (c : ℚ) : bracket f (C c) = 0 := by
  simp [bracket, polyDeriv]

/-- Additivity in the first argument.-/
theorem bracket_add_left (f g k : P) :
    bracket (f + g) k = bracket f k + bracket g k := by
  simp [bracket, polyDeriv] <;> ring

/-- Additivity in the second argument.-/
theorem bracket_add_right (f g k : P) :
    bracket f (g + k) = bracket f g + bracket f k := by
  simp [bracket, polyDeriv] <;> ring

/-- Leibniz rule in the first argument.-/
theorem bracket_mul_left (f g k : P) :
    bracket (f * g) k = f * bracket g k + g * bracket f k := by
  simp [bracket, polyDeriv, MvPolynomial.pderiv_mul] <;> ring

/-- Leibniz rule in the second argument.-/
theorem bracket_mul_right (f g k : P) :
    bracket f (g * k) = g * bracket f k + k * bracket f g := by
  simp [bracket, polyDeriv, MvPolynomial.pderiv_mul] <;> ring

/-- First canonical relation.-/
@[simp] theorem bracket_D_R : bracket D R = 1 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Second canonical relation.-/
@[simp] theorem bracket_S_T : bracket S T = 1 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- First mixed relation.-/
@[simp] theorem bracket_R_S : bracket R S = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Second mixed relation.-/
@[simp] theorem bracket_R_T : bracket R T = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Third mixed relation.-/
@[simp] theorem bracket_D_S : bracket D S = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Fourth mixed relation.-/
@[simp] theorem bracket_D_T : bracket D T = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

@[simp] theorem bracket_R_D : bracket R D = -1 := by
  rw [bracket_skew, bracket_D_R]

@[simp] theorem bracket_T_S : bracket T S = -1 := by
  rw [bracket_skew, bracket_S_T]

@[simp] theorem bracket_S_R : bracket S R = 0 := by
  rw [bracket_skew, bracket_R_S]
  simp

@[simp] theorem bracket_T_R : bracket T R = 0 := by
  rw [bracket_skew, bracket_R_T]
  simp

@[simp] theorem bracket_S_D : bracket S D = 0 := by
  rw [bracket_skew, bracket_D_S]
  simp

@[simp] theorem bracket_T_D : bracket T D = 0 := by
  rw [bracket_skew, bracket_D_T]
  simp

/-- The canonical generator bracket matrix in the order `(x,q,p,z)`.-/
def canonicalMatrix : Var → Var → ℚ :=
  ![![0, 0, -1, 0],
    ![0, 0, 0, -1],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0]]

/-- The bracket of source generators is the canonical matrix.-/
theorem bracket_X_X (i j : Var) :
    bracket (X i) (X j) = C (canonicalMatrix i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [bracket, polyDeriv, canonicalMatrix]

/-- The bracket of output generators is the same canonical matrix.-/
theorem bracket_output_output (i j : Var) :
    bracket (output i) (output j) = C (canonicalMatrix i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [output, canonicalMatrix]

@[simp] theorem Phi_X (i : Var) : Phi (X i) = output i := by
  simp [Phi]

/-- Preservation of brackets on the four polynomial generators.-/
theorem Phi_generator_bracket (i j : Var) :
    bracket (Phi (X i)) (Phi (X j)) = Phi (bracket (X i) (X j)) := by
  rw [Phi_X, Phi_X, bracket_output_output, bracket_X_X]
  simp [Phi]

/-- Preservation against a generator, promoted from generators to all polynomials.-/
lemma Phi_preserves_right_generator (i : Var) (f : P) :
    bracket (Phi f) (Phi (X i)) = Phi (bracket f (X i)) := by
  refine MvPolynomial.induction_on
    (motive := fun h : P =>
      bracket (Phi h) (Phi (X i)) = Phi (bracket h (X i)))
    f ?_ ?_ ?_
  · intro c
    simp
  · intro f g hf hg
    simp only [map_add, bracket_add_left]
    exact congrArg₂ (· + ·) hf hg
  · intro f j hf
    simp only [map_mul, map_add, bracket_mul_left]
    rw [Phi_generator_bracket, hf]

/-- The substitution endomorphism preserves the bracket on all polynomials.-/
theorem Phi_isPoisson : IsPoisson Phi := by
  intro f g
  refine MvPolynomial.induction_on
    (motive := fun h : P =>
      bracket (Phi f) (Phi h) = Phi (bracket f h))
    g ?_ ?_ ?_
  · intro c
    simp
  · intro g k hg hk
    simp only [map_add, bracket_add_right]
    exact congrArg₂ (· + ·) hg hk
  · intro g j hg
    simp only [map_mul, map_add, bracket_mul_right]
    rw [Phi_preserves_right_generator, hg]

end
end RankTwoPoisson
