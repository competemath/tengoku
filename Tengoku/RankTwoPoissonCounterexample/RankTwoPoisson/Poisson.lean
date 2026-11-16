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

/-- The canonical bracket is skew-symmetric.
@isnad1 id=eq.0h2v.s5.4344d2d507aa from=translated src=- shape=da5c3e4f vocab=d227fade
-/
theorem bracket_skew (f g : P) : bracket f g = -bracket g f := by
  simp [bracket] <;> ring

/--
@isnad1 id=eq.0h1v.s4.b62006b03bb0 from=translated src=- shape=b6a79cd4 vocab=fb2863e1
-/
@[simp] theorem bracket_self (f : P) : bracket f f = 0 := by
  simp [bracket] <;> ring

/--
@isnad1 id=eq.0h2v.s6.82283281ece9 from=translated src=- shape=f78bc5af vocab=d27a658f
-/
@[simp] theorem bracket_C_left (c : ℚ) (f : P) : bracket (C c) f = 0 := by
  simp [bracket, polyDeriv]

/--
@isnad1 id=eq.0h2v.s6.ab6aaa49db5c from=translated src=- shape=62c2a2a3 vocab=d27a658f
-/
@[simp] theorem bracket_C_right (f : P) (c : ℚ) : bracket f (C c) = 0 := by
  simp [bracket, polyDeriv]

/-- Additivity in the first argument.
@isnad1 id=eq.0h3v.s6.eda33300380f from=translated src=- shape=2f6dc6a8 vocab=3bfd8445
-/
theorem bracket_add_left (f g k : P) :
    bracket (f + g) k = bracket f k + bracket g k := by
  simp [bracket, polyDeriv] <;> ring

/-- Additivity in the second argument.
@isnad1 id=eq.0h3v.s6.d04d801c880f from=translated src=- shape=4a33f3d9 vocab=3bfd8445
-/
theorem bracket_add_right (f g k : P) :
    bracket f (g + k) = bracket f g + bracket f k := by
  simp [bracket, polyDeriv] <;> ring

/-- Leibniz rule in the first argument.
@isnad1 id=eq.0h3v.s6.595f159cad9c from=translated src=- shape=962336b1 vocab=24c34134
-/
theorem bracket_mul_left (f g k : P) :
    bracket (f * g) k = f * bracket g k + g * bracket f k := by
  simp [bracket, polyDeriv, MvPolynomial.pderiv_mul] <;> ring

/-- Leibniz rule in the second argument.
@isnad1 id=eq.0h3v.s6.04c11fc18eff from=translated src=- shape=48b0d5a0 vocab=24c34134
-/
theorem bracket_mul_right (f g k : P) :
    bracket f (g * k) = g * bracket f k + k * bracket f g := by
  simp [bracket, polyDeriv, MvPolynomial.pderiv_mul] <;> ring

/-- First canonical relation.
@isnad1 id=eq.0h0v.s4.b7dea8187986 from=translated src=- shape=b3c4969c vocab=9b08bfc0
-/
@[simp] theorem bracket_D_R : bracket D R = 1 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Second canonical relation.
@isnad1 id=eq.0h0v.s4.fd28d7c8d318 from=translated src=- shape=b3c4969c vocab=e00ebe9e
-/
@[simp] theorem bracket_S_T : bracket S T = 1 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- First mixed relation.
@isnad1 id=eq.0h0v.s4.d0e848efaa7c from=translated src=- shape=b3c4969c vocab=bf006fe4
-/
@[simp] theorem bracket_R_S : bracket R S = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Second mixed relation.
@isnad1 id=eq.0h0v.s4.af98cbacfa99 from=translated src=- shape=b3c4969c vocab=90ce16e1
-/
@[simp] theorem bracket_R_T : bracket R T = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Third mixed relation.
@isnad1 id=eq.0h0v.s4.c4a8fec278b0 from=translated src=- shape=b3c4969c vocab=09eddbc3
-/
@[simp] theorem bracket_D_S : bracket D S = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/-- Fourth mixed relation.
@isnad1 id=eq.0h0v.s4.6b524768330d from=translated src=- shape=b3c4969c vocab=aeffbb21
-/
@[simp] theorem bracket_D_T : bracket D T = 0 := by
  apply MvPolynomial.funext
  intro v
  simp [bracket, polyDeriv, D, D0, H, R, S, T, u, y, beta, B, a,
    rat, x, q, p, z, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow] <;>
    ring_nf

/--
@isnad1 id=eq.0h0v.s5.0cff2e4ac0d9 from=translated src=- shape=619ac0ea vocab=ded36ccd
-/
@[simp] theorem bracket_R_D : bracket R D = -1 := by
  rw [bracket_skew, bracket_D_R]

/--
@isnad1 id=eq.0h0v.s5.67c9f1b86619 from=translated src=- shape=619ac0ea vocab=65006a9c
-/
@[simp] theorem bracket_T_S : bracket T S = -1 := by
  rw [bracket_skew, bracket_S_T]

/--
@isnad1 id=eq.0h0v.s4.a9351e9dfaa3 from=translated src=- shape=b3c4969c vocab=bf006fe4
-/
@[simp] theorem bracket_S_R : bracket S R = 0 := by
  rw [bracket_skew, bracket_R_S]
  simp

/--
@isnad1 id=eq.0h0v.s4.f722844b2ef6 from=translated src=- shape=b3c4969c vocab=90ce16e1
-/
@[simp] theorem bracket_T_R : bracket T R = 0 := by
  rw [bracket_skew, bracket_R_T]
  simp

/--
@isnad1 id=eq.0h0v.s4.f21db3f76642 from=translated src=- shape=b3c4969c vocab=09eddbc3
-/
@[simp] theorem bracket_S_D : bracket S D = 0 := by
  rw [bracket_skew, bracket_D_S]
  simp

/--
@isnad1 id=eq.0h0v.s4.e97e68853637 from=translated src=- shape=b3c4969c vocab=aeffbb21
-/
@[simp] theorem bracket_T_D : bracket T D = 0 := by
  rw [bracket_skew, bracket_D_T]
  simp

/-- The canonical generator bracket matrix in the order `(x,q,p,z)`.-/
def canonicalMatrix : Var → Var → ℚ :=
  ![![0, 0, -1, 0],
    ![0, 0, 0, -1],
    ![1, 0, 0, 0],
    ![0, 1, 0, 0]]

/-- The bracket of source generators is the canonical matrix.
@isnad1 id=eq.0h2v.s6.41647a2550c4 from=translated src=- shape=09cd99dd vocab=c8c5f244
-/
theorem bracket_X_X (i j : Var) :
    bracket (X i) (X j) = C (canonicalMatrix i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [bracket, polyDeriv, canonicalMatrix]

/-- The bracket of output generators is the same canonical matrix.
@isnad1 id=eq.0h2v.s6.c8c8225e6eb1 from=translated src=- shape=879734e5 vocab=7934a0d4
-/
theorem bracket_output_output (i j : Var) :
    bracket (output i) (output j) = C (canonicalMatrix i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [output, canonicalMatrix]

/--
@isnad1 id=eq.0h1v.s7.ca1d964b9af1 from=translated src=- shape=23a588a8 vocab=a8d8ad5e
-/
@[simp] theorem Phi_X (i : Var) : Phi (X i) = output i := by
  simp [Phi]

/-- Preservation of brackets on the four polynomial generators.
@isnad1 id=eq.0h2v.s8.0198a0edf4d7 from=translated src=- shape=363e88fa vocab=4b28ab0e
-/
theorem Phi_generator_bracket (i j : Var) :
    bracket (Phi (X i)) (Phi (X j)) = Phi (bracket (X i) (X j)) := by
  rw [Phi_X, Phi_X, bracket_output_output, bracket_X_X]
  simp [Phi]

/-- Preservation against a generator, promoted from generators to all polynomials.
@isnad1 id=eq.0h2v.s8.289427239d8e from=translated src=- shape=a89e376f vocab=4b28ab0e
-/
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

/-- The substitution endomorphism preserves the bracket on all polynomials.
@isnad1 id=ispoisso.0h0v.s1.455eeb851505 from=translated src=- shape=49959d42 vocab=69fbd99f
-/
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
