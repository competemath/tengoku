/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Tengoku

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The Fermat quotient

For a prime `p` and an integer `x`, the *Fermat quotient* is the rational number
`q_p(x) = (x ^ (p - 1) - 1) / p`. It is an integer exactly when `p ∤ x`, but the
quotient is taken in `ℚ` so that the definition carries no side condition and the
integrality is a theorem about it rather than part of it.

## Main definitions

* `GranvilleMoore.fermatUnit p x`: the power `t_x = x ^ (p - 1)`. When `p ∤ x` this is a
  principal unit at `p`, i.e. `t_x ≡ 1 [ZMOD p]`; that is what makes it the base of the
  Frobenius tower studied later.
* `GranvilleMoore.fermatQuotient p x`: the Fermat quotient `q_p(x) = (t_x - 1) / p`, a
  rational number.
* `GranvilleMoore.frobeniusExponent p k`: the Frobenius exponent
  `e_k = ∑_{r < k} p ^ r`, the exponent with `t_x ^ (e_k) = x ^ (p ^ k) / x`.

## Implementation notes

`fermatUnit` is an `abbrev`: it is notation for `x ^ (p - 1)` and has nothing to say
about itself, so every `pow` lemma in Mathlib applies to it unchanged.

`fermatQuotient` is `ℚ`-valued and unconditional; `(p : ℚ) ≠ 0` is needed only to
cancel the denominator, see `GranvilleMoore.natCast_mul_fermatQuotient`.
-/

@[expose] public section

namespace GranvilleMoore

open Finset

/-- The unit attached to an integer `x` at `p`: the power `t_x = x ^ (p - 1)`.

For `p` prime with `p ∤ x` this is a principal unit at `p`, congruent to `1` modulo `p`
by Fermat's little theorem. -/
abbrev fermatUnit (p : ℕ) (x : ℤ) : ℤ := x ^ (p - 1)

/-- The Fermat quotient of an integer `x` at `p`:
`q_p(x) = (x ^ (p - 1) - 1) / p`, the quotient being taken in `ℚ`.

For `p` prime with `p ∤ x` this rational number is an integer. -/
def fermatQuotient (p : ℕ) (x : ℤ) : ℚ := ((fermatUnit p x - 1 : ℤ) : ℚ) / (p : ℚ)

/-- The Fermat quotient written out with the numerator cast to `ℚ` termwise.
@isnad1 id=eq.0h2v.s5.b0f14c60c1c4 from=translated src=- shape=3ba757f2 vocab=1bed41f6
-/
theorem fermatQuotient_eq_div (p : ℕ) (x : ℤ) :
    fermatQuotient p x = ((x : ℚ) ^ (p - 1) - 1) / (p : ℚ) := by
  rw [fermatQuotient]
  push_cast
  ring

/-- Cancelling the denominator in the Fermat quotient: this is the identity
`x ^ (p - 1) = 1 + p * q_p(x)` in `ℚ`, and the only property of `fermatQuotient`
its consumers need.
@isnad1 id=eq.1h2v.s6.f90db910d4fb from=translated src=- shape=fe61eea4 vocab=e247b179
-/
theorem natCast_mul_fermatQuotient {p : ℕ} (hp : p ≠ 0) (x : ℤ) :
    (p : ℚ) * fermatQuotient p x = (x : ℚ) ^ (p - 1) - 1 := by
  rw [fermatQuotient_eq_div, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hp)]

/-- The Fermat quotient of `1` vanishes: `q_p(1) = 0`.
@isnad1 id=eq.0h1v.s4.4d044ccff876 from=translated src=- shape=59ae2d96 vocab=b6f28ce1
-/
@[simp]
theorem fermatQuotient_one (p : ℕ) : fermatQuotient p 1 = 0 := by
  rw [fermatQuotient_eq_div]
  simp

/-- The Frobenius exponent `e_k = ∑_{r < k} p ^ r`, so that `e₀ = 0` and `e₁ = 1`.

It is the exponent for which `(x ^ (p - 1)) ^ e_k = x ^ (p ^ k - 1)`, since
`(p - 1) * e_k = p ^ k - 1`. -/
def frobeniusExponent (p k : ℕ) : ℕ := ∑ r ∈ range k, p ^ r

/-- The Frobenius exponent is the truncated geometric sum, which is how Mathlib's
geometric-sum API applies to it.
@isnad1 id=eq.0h2v.s4.9b6784948b6a from=translated src=- shape=dcc7b5aa vocab=f2eddf4f
-/
theorem frobeniusExponent_eq_sum (p k : ℕ) :
    frobeniusExponent p k = ∑ r ∈ range k, p ^ r := rfl

/-- The Frobenius exponent of the empty tower vanishes: `e_0 = 0`.
@isnad1 id=eq.0h1v.s4.1f1035567f6d from=translated src=- shape=1d838610 vocab=5e4ea37b
-/
@[simp]
theorem frobeniusExponent_zero (p : ℕ) : frobeniusExponent p 0 = 0 := by
  rw [frobeniusExponent_eq_sum, range_zero, sum_empty]

/-- The first Frobenius exponent is `1`: `e_1 = 1`.
@isnad1 id=eq.0h1v.s4.273f793d2e3d from=translated src=- shape=1d838610 vocab=5e4ea37b
-/
@[simp]
theorem frobeniusExponent_one (p : ℕ) : frobeniusExponent p 1 = 1 := by
  rw [frobeniusExponent_eq_sum]
  simp

/-- The recursion `e_{k+1} = e_k + p ^ k` defining the Frobenius exponent.
@isnad1 id=eq.0h2v.s5.51a09fc7e927 from=translated src=- shape=ce6e45c1 vocab=52fe19a6
-/
theorem frobeniusExponent_succ (p k : ℕ) :
    frobeniusExponent p (k + 1) = frobeniusExponent p k + p ^ k := by
  rw [frobeniusExponent_eq_sum, frobeniusExponent_eq_sum, sum_range_succ]

/-- Peeling the recursion off the bottom instead: `e_{k+1} = 1 + p * e_k`.
@isnad1 id=eq.0h2v.s5.98b64e0a3b32 from=translated src=- shape=e18b43e7 vocab=e6ee4c28
-/
theorem frobeniusExponent_succ' (p k : ℕ) :
    frobeniusExponent p (k + 1) = 1 + p * frobeniusExponent p k := by
  rw [frobeniusExponent_eq_sum, frobeniusExponent_eq_sum, geom_sum_succ, add_comm]

end GranvilleMoore
