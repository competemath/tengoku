import Tengoku.MagicSquaresFieldsLean.MagicSquares.Certificates.DensePolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates.DensePolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- One binary-exponentiation step, with its exact division identity.-/
structure PowStep (R : Type*) where
  bit : Bool
  value : List R
  quotient : List R

def exponent (n : ℕ) : List (PowStep R) → ℕ
  | [] => n
  | s :: rest => exponent (2 * n + if s.bit then 1 else 0) rest

def checkPow [DecidableEq R] (f r : List R) : List (PowStep R) → Bool
  | [] => eqCheck r [0, 1]
  | s :: rest =>
    eqCheck (mul (mul r r) (if s.bit then [0, 1] else [1]))
      (add s.value (mul f s.quotient)) && checkPow f s.value rest

/--
@isnad1 id=eq.3h8v.s7.d855b2355f96 from=translated src=- shape=1b39d58c vocab=ad8ce3b3
-/
theorem checkPow_sound [DecidableEq R] (h : R →+* S) (x : S)
    {f r : List R} {steps : List (PowStep R)} (hc : checkPow f r steps = true)
    (hf : eval h x f = 0) {n : ℕ} (hr : eval h x r = x ^ n) :
    x ^ exponent n steps = x := by
  induction steps generalizing r n with
  | nil =>
    have hz := eqCheck_sound h x hc
    simpa [exponent, eval, hr] using hz
  | cons s rest ih =>
    simp only [checkPow, Bool.and_eq_true] at hc
    apply ih hc.2
    have hz := eqCheck_sound h x hc.1
    cases hb : s.bit <;>
      simpa [eval_add, eval_mul, hf, hr, eval, hb, pow_add, pow_mul, pow_two,
        mul_comm, mul_left_comm, mul_assoc] using hz.symm

/-- A short modular-power trace proves the defining polynomial divides
`X^q-X`; no irreducibility assumption is needed for positive certificates.
@isnad1 id=dvd.1h3v.s7.a896cc38d8d0 from=translated src=- shape=77b0cf7b vocab=b95e4b7a
-/
theorem dvd_X_pow_sub_X_of_check [DecidableEq R] {f : List R}
    {steps : List (PowStep R)} (hc : checkPow f [1] steps = true) :
    poly f ∣ (Polynomial.X ^ exponent 0 steps - Polynomial.X : Polynomial R) := by
  let fp := poly f
  have hf : eval (AdjoinRoot.of fp) (AdjoinRoot.root fp) f = 0 := by
    rw [← eval_poly]
    exact AdjoinRoot.eval₂_root fp
  have hr : eval (AdjoinRoot.of fp) (AdjoinRoot.root fp) [1] =
      AdjoinRoot.root fp ^ 0 := by simp [eval]
  have hp := checkPow_sound (AdjoinRoot.of fp) (AdjoinRoot.root fp) hc hf hr
  apply AdjoinRoot.mk_eq_zero.mp
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] using hp

end MagicSquares.Certificates.DensePolynomial
