import Tengoku.Seed.RingTheory.Polynomial.Chebyshev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The native rescaled second-kind Chebyshev polynomial sequence

The nonnegative-index `Polynomial.Chebyshev.S` polynomials are monic of the
matching degree. Thus Mathlib's native `Polynomial.Sequence` and its basis API
apply directly, with no new polynomial definition.
-/

noncomputable section
set_option autoImplicit false

namespace Polynomial.Chebyshev

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- The native rescaled second-kind Chebyshev polynomial at a nonnegative
index has that exact degree, over every nontrivial commutative ring.
@isnad1 id=eq.0h2v.s5.3d0104ba0d47 from=translated src=- shape=b8f8a83d vocab=293271cd
-/
@[simp]
theorem degree_S_natCast (n : ℕ) : (S R (n : ℤ)).degree = n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_cast; simp
  | more n hn hn1 =>
    have hRec : S R ((n + 2 : ℕ) : ℤ) =
        X * S R ((n + 1 : ℕ) : ℤ) - S R (n : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using S_add_two R (n : ℤ)
    have hMain : (X * S R ((n + 1 : ℕ) : ℤ)).degree = ((n + 2 : ℕ) : WithBot ℕ) := by
      rw [mul_comm, degree_mul_X, hn1]
      norm_cast
    rw [hRec, degree_sub_eq_left_of_degree_lt]
    · exact hMain
    · rw [hn, hMain]
      norm_cast
      omega

/-- The native rescaled second-kind Chebyshev polynomials at nonnegative
indices are monic.
@isnad1 id=monic.0h2v.s4.94d3c1d23173 from=translated src=- shape=88b70c49 vocab=e3b2778d
-/
theorem monic_S_natCast (n : ℕ) : (S R (n : ℤ)).Monic := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ hn1 =>
    have hRec : S R ((n + 2 : ℕ) : ℤ) =
        X * S R ((n + 1 : ℕ) : ℤ) - S R (n : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using S_add_two R (n : ℤ)
    rw [hRec]
    apply (monic_X.mul hn1).sub_of_left
    rw [mul_comm, degree_mul_X, degree_S_natCast, degree_S_natCast]
    norm_cast
    omega

/-- The existing rescaled second-kind Chebyshev polynomials as Mathlib's
native polynomial sequence. Its native `Sequence.basis` is available because
the leading coefficients are one.-/
noncomputable def chebyshevSsequence : Polynomial.Sequence R where
  elems' n := S R (n : ℤ)
  degree_eq' := degree_S_natCast R

/-- Evaluation of the native sequence adapter introduces no new polynomial.
@isnad1 id=eq.0h2v.s5.0ead70cb99ed from=translated src=- shape=0c89638a vocab=671af95c
-/
@[simp]
theorem chebyshevSsequence_apply (n : ℕ) : chebyshevSsequence R n = S R (n : ℤ) := rfl

end Polynomial.Chebyshev
