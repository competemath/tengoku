/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.Algebra.Group.Int.Even
import Tengoku.Seed.Data.Int.ModEq
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer Parity Helpers

Material destined for mathlib.
-/

/-- Normalise the integer half of `-b` when `b` is even.
@isnad1 id=eq.1h1v.s5.029e71a67f9d from=translated src=- shape=7eefaabe vocab=bf6e0c95
-/
-- Repository use: Cox ideal formulas use this to recover the integer parameter
-- from the middle coefficient in the non-half-integral branch.
theorem Int.two_mul_neg_ediv_two_of_even {b : ℤ} (hb : Even b) : 2 * ((-b) / 2) = -b :=
  Int.two_mul_ediv_two_of_even hb.neg

/-- Normalise the integer half of `-(b + 1)` when `b` is odd.
@isnad1 id=eq.1h1v.s6.a47ae11a6650 from=translated src=- shape=a5aa3af8 vocab=e17c49a5
-/
-- Repository use: Cox ideal formulas use this to recover the integer parameter
-- from the middle coefficient in the half-integral branch.
theorem Int.two_mul_neg_succ_ediv_two_of_odd {b : ℤ} (hb : Odd b) :
    2 * (-(b + 1) / 2) = -(b + 1) := by
  have hb_even : Even (b + 1) := by
    simpa using hb.add_odd (show Odd (1 : ℤ) by exact odd_one)
  exact Int.two_mul_ediv_two_of_even hb_even.neg

/-- An integer congruent modulo an even modulus to an even integer is even.
@isnad1 id=even.2h3v.s5.51f369b218a9 from=translated src=- shape=b633b253 vocab=5c18c152
-/
-- Repository use: `composeMiddleB` parity in computable Gauss composition.
theorem Int.even_of_modEq_even {B b a : ℤ} (hb : Even b) (hB : B ≡ b [ZMOD 2 * a]) :
    Even B := by
  rcases hb with ⟨m, hm⟩
  rcases Int.modEq_iff_dvd.mp hB with ⟨k, hk⟩
  refine ⟨m - a * k, ?_⟩
  have hB_eq : B = b - 2 * a * k := by linarith
  rw [hB_eq, hm]
  ring

/-- An integer congruent modulo an even modulus to an odd integer is odd.
@isnad1 id=odd.2h3v.s5.d2decf03c710 from=translated src=- shape=b633b253 vocab=2749c0f8
-/
-- Repository use: `composeMiddleB` parity in computable Gauss composition.
theorem Int.odd_of_modEq_odd {B b a : ℤ} (hb : Odd b) (hB : B ≡ b [ZMOD 2 * a]) :
    Odd B := by
  rcases hb with ⟨m, hm⟩
  rcases Int.modEq_iff_dvd.mp hB with ⟨k, hk⟩
  refine ⟨m - a * k, ?_⟩
  have hB_eq : B = b - 2 * a * k := by linarith
  rw [hB_eq, hm]
  ring

/-- If twice an integer is a square, then the integer is twice a square.
@isnad1 id=ex.1h2v.s6.6299904435cc from=translated src=- shape=588ac586 vocab=36c32c22
-/
-- Repository use: Heegner's Diophantine reduction uses this in the odd
-- `X` branch to pass from `2 * (X ^ 3 + 1)` being a square to
-- `X ^ 3 + 1` being twice a square.
theorem Int.exists_eq_two_mul_sq_of_two_mul_eq_sq {A z : ℤ}
    (h : 2 * A = z ^ 2) :
    ∃ w : ℤ, A = 2 * w ^ 2 := by
  have hz_even_sq : Even (z ^ 2) := by
    rw [← h]
    exact even_two_mul A
  have hz_even : Even z :=
    (Int.even_pow' (m := z) (n := 2) (by norm_num)).mp hz_even_sq
  rcases hz_even with ⟨w, hw⟩
  use w
  subst z
  nlinarith

/-- If twice an integer is the negative of a square, then the integer is
negative twice a square.
@isnad1 id=ex.1h2v.s6.f7ee4ab52793 from=translated src=- shape=517f065b vocab=02ee4123
-/
-- Repository use: Heegner's Diophantine reduction uses this in the odd
-- `X` branch to pass from `2 * (X ^ 3 + 1)` being a negative square to
-- `X ^ 3 + 1` being negative twice a square.
theorem Int.exists_eq_neg_two_mul_sq_of_two_mul_eq_neg_sq {A z : ℤ}
    (h : 2 * A = -z ^ 2) :
    ∃ w : ℤ, A = -2 * w ^ 2 := by
  have hneg : 2 * (-A) = z ^ 2 := by
    nlinarith
  obtain ⟨w, hw⟩ := Int.exists_eq_two_mul_sq_of_two_mul_eq_sq hneg
  use w
  nlinarith

/-- If an integer cube is one more than a square, then the square root is even.
@isnad1 id=even.1h2v.s5.e1234b2a04f0 from=translated src=- shape=6ebb7c7f vocab=dbe1dbc9
-/
-- Repository use: Cox's Gaussian-integer auxiliary equation uses this before
-- proving the two factors `z ± √-1` are coprime.
theorem Int.even_of_cube_eq_sq_add_one {n z : ℤ} (h : n ^ 3 = z ^ 2 + 1) :
    Even z := by
  by_contra hz_even
  have hz_odd : Odd z := Int.not_even_iff_odd.mp hz_even
  rcases hz_odd with ⟨k, hk⟩
  subst z
  have hn3_even : Even (n ^ 3) := by
    rw [h]
    use 2 * k ^ 2 + 2 * k + 1
    ring
  have hn_even : Even n := (Int.even_pow' (m := n) (n := 3) (by norm_num)).mp hn3_even
  rcases hn_even with ⟨m, hm⟩
  subst n
  have hhalf : 4 * m ^ 3 = 2 * k ^ 2 + 2 * k + 1 := by nlinarith
  have hleft_even : Even (4 * m ^ 3) := by
    use 2 * m ^ 3
    ring
  have hright_odd : Odd (2 * k ^ 2 + 2 * k + 1) := by
    use k ^ 2 + k
    ring
  rw [hhalf] at hleft_even
  exact (Int.not_even_iff_odd.mpr hright_odd) hleft_even

/-- If an integer cube is one more than a square, then the cube root is odd.
@isnad1 id=odd.1h2v.s5.89930c28f476 from=translated src=- shape=7efb14cb vocab=5eb17a74
-/
-- Repository use: Cox's Gaussian-integer auxiliary equation uses this together
-- with `Int.even_of_cube_eq_sq_add_one` to control common divisors of
-- `z ± √-1`.
theorem Int.odd_of_cube_eq_sq_add_one {n z : ℤ} (h : n ^ 3 = z ^ 2 + 1) :
    Odd n := by
  obtain ⟨k, hk⟩ := Int.even_of_cube_eq_sq_add_one h
  subst z
  have hn3_odd : Odd (n ^ 3) := by
    rw [h]
    use 2 * k ^ 2
    ring
  exact (Int.odd_pow' (m := n) (n := 3) (by norm_num)).mp hn3_odd

/-- If an integer cube is one more than twice a square, then the cube root is odd.
@isnad1 id=odd.1h2v.s6.3c937d46da31 from=translated src=- shape=0d125d0d vocab=533e4da7
-/
-- Repository use: Cox's `ℤ[√-2]` auxiliary equation uses this to control common
-- divisors of `1 ± z√-2`.
theorem Int.odd_of_cube_eq_two_mul_sq_add_one {n z : ℤ}
    (h : n ^ 3 = 2 * z ^ 2 + 1) :
    Odd n := by
  by_contra hn_odd
  have hn_even : Even n := Int.not_odd_iff_even.mp hn_odd
  have hn3_even : Even (n ^ 3) := (Int.even_pow' (m := n) (n := 3) (by norm_num)).mpr hn_even
  have hrhs_odd : Odd (2 * z ^ 2 + 1) := by
    use z ^ 2
  rw [h] at hn3_even
  exact (Int.not_even_iff_odd.mpr hrhs_odd) hn3_even
