/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic exclusions for the two pairs starting at P + a

These are integer lemmas for the four-prime argument for Erdos problem 700.
They do not assume Lucas's theorem, primality, or the result to be proved.
Their hypotheses are the concrete inequalities obtained after normalizing
base-q digits.  The digit extraction and its range checks are separate.
-/

namespace Erdos700.FourPrime.PairA

/-- The zero-carry branch for the pair `(P+a, P+b)` is impossible.
The hypotheses are respectively the congruence lower bound on `v`, the
normalized high digit bound, and the normalized middle digit bound.
@isnad1 id=false.6h5v.s7.56313ec62857 from=translated src=- shape=96628a17 vocab=e94596d0
-/
theorem pairAB_h0_impossible
    (a b c u v : ℤ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hv : (b - a) * u ≤ v)
    (hu : u ≤ a + c - 3 * b)
    (hmiddle : (2 * b - a) * c + 2 * a * b - 3 * b ^ 2 ≤
      3 * (b - a) * u - v) : False := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hscale := mul_le_mul_of_nonneg_left hu
    (show (0 : ℤ) ≤ 2 * (b - a) by positivity)
  have hfirst : 0 < a * (c - b) := mul_pos ha (sub_pos.mpr hbc)
  have hsecond : 0 ≤ a * (b - a) := mul_nonneg ha.le hd.le
  have hthird : 0 ≤ (b - a) ^ 2 := sq_nonneg (b - a)
  nlinarith

/-- The one-carry branch for `(P+a, P+b)` is impossible.
This version has already cancelled the positive factor `b-a` from the
low digit inequality.
@isnad1 id=false.4h5v.s8.4855e5e730bd from=translated src=- shape=945026f6 vocab=e94596d0
-/
theorem pairAB_h1_impossible
    (a b c u v : ℤ) (hab : a < b)
    (hlow : 2 * (b - a) * u - v - 1 ≤ b * (c - b))
    (hmiddle : (2 * b - a) * c + 2 * a * b - 3 * b ^ 2 ≤
      3 * (b - a) * u - v - 1)
    (hhigh : u ≤ a + c - 3 * b) : False := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hscale := mul_le_mul_of_nonneg_left hhigh hd.le
  have hsq : 0 < (b - a) ^ 2 := sq_pos_of_pos hd
  nlinarith

/-- The zero-carry contradiction in the exact normalized digit notation.
@isnad1 id=false.6h6v.s8.110e299e15d3 from=translated src=- shape=c79c13b4 vocab=e94596d0
-/
theorem pairAB_h0_from_digits
    (a b c q u v : ℤ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hv : (b - a) * u ≤ v)
    (hhigh : u - 1 ≤ a + c - 3 * b - 1)
    (hmiddle : q + (v - 3 * (b - a) * u) ≤
      q - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2)) : False := by
  apply pairAB_h0_impossible a b c u v ha hab hbc hv
  · linarith
  · linarith

/-- The one-carry contradiction in the exact normalized digit notation,
including cancellation of the positive low digit factor.
@isnad1 id=false.4h6v.s8.cbf9364978c7 from=translated src=- shape=6c1b459c vocab=e94596d0
-/
theorem pairAB_h1_from_digits
    (a b c q u v : ℤ) (hab : a < b)
    (hlow : (b - a) * (2 * (b - a) * u - v - 1) ≤
      b * (b - a) * (c - b))
    (hhigh : u - 1 ≤ a + c - 3 * b - 1)
    (hmiddle : q + (v - 3 * (b - a) * u + 1) ≤
      q - ((2 * b - a) * c + 2 * a * b - 3 * b ^ 2)) : False := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hlow' : 2 * (b - a) * u - v - 1 ≤ b * (c - b) := by
    apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith only [hlow]
  apply pairAB_h1_impossible a b c u v hab hlow'
  · linarith
  · linarith

/-- Exact factorization of the gap that excludes a negative low coefficient
for the pair `(P+a, P+c)`.
@isnad1 id=eq.0h3v.s7.d50860081fb5 from=translated src=- shape=bf99e1f9 vocab=fb2191f5
-/
theorem pairAC_low_gap_identity (a b c : ℤ) :
    c * (c - a) * (c - b) -
      (c - a) * (b * c - 2 * a * (b + c) + 3 * a ^ 2) =
    (c - a) ^ 2 * (c + 3 * a - 2 * b) := by
  ring

/-- In the negative-constant branch of `(P+a,P+c)`, the normalized low
q-digit `q + K` cannot be at most `q - F`.  The sign of `K` itself is
unneeded once this normalized low-digit inequality has been supplied.
@isnad1 id=false.5h7v.s8.2e3020a1e57c from=translated src=- shape=02aacf82 vocab=e94596d0
-/
theorem pairAC_negative_low_impossible
    (a b c q u v h : ℤ)
    (hac : a < c) (hsep : 0 < c + 3 * a - 2 * b)
    (hu : 0 ≤ u)
    (hvh : v + h ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2)
    (hlow : q + (c - a) * (2 * (c - a) * u - v - h) ≤
      q - c * (c - a) * (c - b)) : False := by
  have hd : 0 < c - a := sub_pos.mpr hac
  have hdu : 0 ≤ (c - a) * u := mul_nonneg hd.le hu
  have hinner : -(b * c - 2 * a * (b + c) + 3 * a ^ 2) ≤
      2 * (c - a) * u - v - h := by
    nlinarith
  have hscale := mul_le_mul_of_nonneg_left hinner hd.le
  have hgap : 0 < (c - a) ^ 2 * (c + 3 * a - 2 * b) :=
    mul_pos (sq_pos_of_pos hd) hsep
  nlinarith

/-- The actual bounds on `v` and the carry `h` imply the bound used in
`pairAC_negative_low_impossible`.
@isnad1 id=le.2h5v.s7.a98d420d439d from=translated src=- shape=cce95a6d vocab=35ae5b9f
-/
theorem pairAC_v_plus_h_bound
    (a b c v h : ℤ)
    (hv : v ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 - 1)
    (hh : h ≤ 1) :
    v + h ≤ b * c - 2 * a * (b + c) + 3 * a ^ 2 := by
  linarith

/-- If the constant coefficient in `(P+a,P+c)` is nonnegative and `u>0`,
the unnormalized middle coefficient is strictly negative.
@isnad1 id=lt.3h5v.s7.09e4906d8695 from=translated src=- shape=06de9b36 vocab=3b732f86
-/
theorem pairAC_middle_negative
    (a c u v h : ℤ)
    (hac : a < c) (hu : 0 < u)
    (hconstant : 0 ≤ (c - a) * (2 * (c - a) * u - v - h)) :
    v - 3 * (c - a) * u + h < 0 := by
  have hd : 0 < c - a := sub_pos.mpr hac
  have hinner : 0 ≤ 2 * (c - a) * u - v - h :=
    (mul_nonneg_iff_of_pos_left hd).mp hconstant
  have hdu : 0 < (c - a) * u := mul_pos hd hu
  nlinarith

/-- The exceptional `u=0` case with nonnegative constant coefficient has
only zero `v` and zero carry.
@isnad1 id=and.4h4v.s6.7bc410014986 from=translated src=- shape=0a1b168b vocab=b4d30996
-/
theorem pairAC_zero_u
    (a c v h : ℤ) (hac : a < c)
    (hv : 0 ≤ v) (hh : 0 ≤ h)
    (hconstant : 0 ≤ (c - a) * (2 * (c - a) * 0 - v - h)) :
    v = 0 ∧ h = 0 := by
  have hd : 0 < c - a := sub_pos.mpr hac
  have hinner : 0 ≤ 2 * (c - a) * 0 - v - h :=
    (mul_nonneg_iff_of_pos_left hd).mp hconstant
  constructor <;> nlinarith

/-- A uniform lower bound on the middle coefficient.
@isnad1 id=le.6h5v.s7.ac9b4a27c611 from=translated src=- shape=ff838385 vocab=e67f7605
-/
theorem pairAC_middle_lower_bound
    (a c u v h : ℤ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hu_upper : u ≤ 2 * c)
    (hv : 0 ≤ v) (hh : 0 ≤ h) :
    -(6 * c ^ 2) ≤ v - 3 * (c - a) * u + h := by
  have hau : 0 ≤ a * u := mul_nonneg ha hu
  have hcu := mul_le_mul_of_nonneg_left hu_upper hc
  nlinarith

/-- A normalized middle digit of the form `q + M` is too large for the
last base.  The actual global threshold `P>=100*c^5` easily implies the
weaker local size hypothesis here.
@isnad1 id=false.9h7v.s8.6d77ecf19396 from=translated src=- shape=eb34461c vocab=e94596d0
-/
theorem pairAC_middle_digit_impossible
    (a b c q u v h : ℤ)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hu_upper : u ≤ 2 * c)
    (hv : 0 ≤ v) (hh : 0 ≤ h)
    (hq : 9 * c ^ 2 < q)
    (hU : 3 * c ^ 2 - 2 * c * (a + b) + a * b ≤ 3 * c ^ 2)
    (hmiddle : q + (v - 3 * (c - a) * u + h) ≤
      (3 * c ^ 2 - 2 * c * (a + b) + a * b) - 1) : False := by
  have hbound := pairAC_middle_lower_bound a c u v h ha hc hu hu_upper hv hh
  linarith

end Erdos700.FourPrime.PairA
