import Tengoku.PaperCLean.PaperC.Arithmetic.ParityVector
import Tengoku.Seed.Data.Nat.Factorization.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Prime-parity support of a square times a defect part

Proposition 3.2 writes every defective integer as `n = s * a^2`, where the
prime divisors of `s` belong to the enumerated small primes.  This file proves
the exact coverage statement required by `DefectCodeRank`: every nonzero
coordinate of the parity vector of `n` already occurs among the prime divisors
of `s`.

Squarefreeness of `s` is not needed for this implication; it is relevant to
the arithmetic counting elsewhere in the proposition.
-/

namespace PaperC
namespace DefectParitySupport

/-- Multiplying a nonzero integer by a square does not change its parity vector.
@isnad1 id=eq.2h2v.s6.1417e4219751 from=translated src=- shape=7d13d2a5 vocab=8d2c7b59
-/
theorem parityVec_mul_sq
    {s a : ℕ} (hs : s ≠ 0) (ha : a ≠ 0) :
    parityVec (s * a ^ 2) = parityVec s := by
  rw [parityVec_mul hs (pow_ne_zero 2 ha), parityVec_pow_two, add_zero]

/--
Every nonzero parity coordinate of `s * a^2` corresponds to a divisor of
`s`.
@isnad1 id=dvd.3h3v.s6.68623322b675 from=translated src=- shape=75a1ce0d vocab=ec74512d
-/
theorem dvd_of_parityVec_mul_sq_ne_zero
    {s a p : ℕ} (hs : s ≠ 0) (ha : a ≠ 0)
    (hp : parityVec (s * a ^ 2) p ≠ 0) :
    p ∣ s := by
  rw [parityVec_mul_sq hs ha, parityVec_apply] at hp
  apply Nat.dvd_of_factorization_pos
  intro hzero
  rw [hzero] at hp
  simp at hp

/--
Transport the preceding divisor statement across an explicit representation
`n = s * a^2`.
@isnad1 id=dvd.4h4v.s6.68b21d818280 from=translated src=- shape=2f5869f2 vocab=ec74512d
-/
theorem dvd_defectPart_of_eq_mul_sq_of_parityVec_ne_zero
    {n s a p : ℕ} (hs : s ≠ 0) (ha : a ≠ 0)
    (hn : n = s * a ^ 2)
    (hp : parityVec n p ≠ 0) :
    p ∣ s := by
  rw [hn] at hp
  exact dvd_of_parityVec_mul_sq_ne_zero hs ha hp

/--
A nonzero coordinate of a parity vector is necessarily indexed by a prime.
Non-prime coordinates of `Nat.factorization` vanish by definition.
@isnad1 id=prime.1h2v.s6.588aac1e01de from=translated src=- shape=b3959fc8 vocab=f1966fa1
-/
theorem prime_of_parityVec_ne_zero
    {n p : ℕ} (hp : parityVec n p ≠ 0) :
    Nat.Prime p := by
  by_contra hprime
  simp only [parityVec_apply,
    Nat.factorization_eq_zero_of_not_prime n hprime, Nat.cast_zero] at hp
  exact hp rfl

/--
If an enumeration covers every prime divisor of the defect part `s`, it
covers every nonzero parity coordinate of `n = s * a^2`.
@isnad1 id=ex.5h6v.s7.445a4d6ff34f from=translated src=- shape=62f16406 vocab=f0e78fb0
-/
theorem parityCoverage_of_eq_mul_sq
    {r n s a : ℕ} (smallPrime : Fin r → ℕ)
    (hs : s ≠ 0) (ha : a ≠ 0)
    (hn : n = s * a ^ 2)
    (hsmall : ∀ p, Nat.Prime p → p ∣ s →
      ∃ j : Fin r, smallPrime j = p) :
    ∀ p, parityVec n p ≠ 0 →
      ∃ j : Fin r, smallPrime j = p := by
  intro p hp
  exact hsmall p (prime_of_parityVec_ne_zero hp)
    (dvd_defectPart_of_eq_mul_sq_of_parityVec_ne_zero
      hs ha hn hp)

end DefectParitySupport
end PaperC
