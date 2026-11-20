/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.Seed.RingTheory.Polynomial.DegreeLT

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial coefficient lemmas used by the Legendre argument

This module contains only the bounded-degree and top-coefficient facts used by
the public ternary proof.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u

/--
@isnad1 id=lt.2h3v.s6.09d3f1982e7d from=translated src=- shape=24d22a72 vocab=2b7ea688
-/
theorem polynomial_natDegree_lt_of_mem_degreeLT
    {R : Type u} [Semiring R] {n : ℕ} {p : Polynomial R}
    (hp : p ∈ Polynomial.degreeLT R n) (hp0 : p ≠ 0) :
    p.natDegree < n := by
  have hdeg := Polynomial.mem_degreeLT.mp hp
  rwa [Polynomial.degree_eq_natDegree hp0, Nat.cast_lt] at hdeg

/--
@isnad1 id=eq.2h5v.s6.63eabb6b9838 from=translated src=- shape=486a05eb vocab=d123fbb3
-/
theorem polynomial_coeff_mul_eq_coeff_mul_of_natDegree_eq
    {R : Type u} [Semiring R] {m n : ℕ} {p q : Polynomial R}
    (hp : p.natDegree = m) (hq : q.natDegree = n) :
    (p * q).coeff (m + n) = p.coeff m * q.coeff n := by
  simpa [Polynomial.leadingCoeff, hp, hq] using
    Polynomial.coeff_mul_degree_add_degree p q

/--
@isnad1 id=eq.0h2v.s6.502c020277e3 from=translated src=- shape=e32d3781 vocab=fe0e5afa
-/
theorem polynomial_coeff_sq_natDegree_mul_two
    {R : Type u} [Semiring R] {p : Polynomial R} :
    (p ^ 2).coeff (2 * p.natDegree) = p.leadingCoeff ^ 2 := by
  have hmul :=
    polynomial_coeff_mul_eq_coeff_mul_of_natDegree_eq
      (p := p) (q := p) rfl rfl
  simp [pow_two, two_mul] at hmul ⊢

/--
@isnad1 id=eq.1h3v.s6.b53b84d634e3 from=translated src=- shape=8abd0b44 vocab=fe0e5afa
-/
theorem polynomial_coeff_sq_natDegree_mul_two_at
    {R : Type u} [Semiring R] {p : Polynomial R} {k : ℕ}
    (hk : 2 * p.natDegree = k) :
    (p ^ 2).coeff k = p.leadingCoeff ^ 2 := by
  subst k
  exact polynomial_coeff_sq_natDegree_mul_two

/--
@isnad1 id=eq.2h5v.s7.45e6d11d95a2 from=translated src=- shape=8161b8c1 vocab=08c17ef1
-/
theorem polynomial_coeff_sq_add_mul_of_top_degrees
    {R : Type u} [Semiring R] {u B C : Polynomial R} {k : ℕ}
    (hu : 2 * u.natDegree = k)
    (hBC : B.natDegree + C.natDegree = k) :
    (u ^ 2 + B * C).coeff k =
      u.leadingCoeff ^ 2 + B.leadingCoeff * C.leadingCoeff := by
  rw [Polynomial.coeff_add]
  rw [polynomial_coeff_sq_natDegree_mul_two_at hu]
  rw [← hBC]
  rw [polynomial_coeff_mul_eq_coeff_mul_of_natDegree_eq (p := B) (q := C) rfl rfl]
  rw [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree]

end RatFunc
end RatFuncWittLocalGlobal
