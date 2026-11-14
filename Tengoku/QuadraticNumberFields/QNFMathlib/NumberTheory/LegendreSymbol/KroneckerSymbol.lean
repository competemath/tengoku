/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.Seed.Data.Nat.Factorization.Basic
import Tengoku.Seed.NumberTheory.LegendreSymbol.JacobiSymbol
import Tengoku.Seed.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kronecker Symbol

Material destined for mathlib.

This file defines the Kronecker symbol for arbitrary integer numerators and
denominators. The natural-denominator core extends the Jacobi symbol by the
supplementary value at `2`; the integer interface adds the conventions at
`-1` and `0`.

## Main definitions

* `kroneckerTwo`: the supplementary Kronecker value `(D / 2)`.
* `kroneckerNegOne`: the supplementary Kronecker value `(D / -1)`.
* `kroneckerSymNat`: the Kronecker symbol `(D / n)` with natural denominator `n`.
* `kroneckerSym`: the Kronecker symbol `(D / n)` with integer denominator `n`.

## Main results

* `kroneckerSym_zero_right`, `kroneckerSym_one_right`,
  `kroneckerSym_neg_one_right`: the exceptional denominator values.
* `kroneckerSymNat_two`: `(D / 2)` is the supplementary value.
* `kroneckerTwo_eq_zero_iff`, `kroneckerTwo_eq_one_iff`,
  `kroneckerTwo_eq_neg_one_iff`: the mod-8 supplementary law.
* `kroneckerSym_natCast`, `kroneckerSym_neg_natCast`: reduction of integer
  denominators to `kroneckerSymNat`.
* `kroneckerSymNat_eq_legendreSym_of_ne_two`,
  `kroneckerSym_eq_legendreSym_of_ne_two`: for an odd prime `p`, `(D / p)` is the
  Legendre symbol `legendreSym p D`.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
/-- The supplementary Kronecker value `(D / 2)`: zero for even `D`, and otherwise
determined by `D % 8` (`1` for `D ≡ ±1 [ZMOD 8]`, `-1` for `D ≡ ±3 [ZMOD 8]`).-/
def _root_.Tengoku.QuadraticNumberFields.kroneckerTwo (D : ℤ) : ℤ :=
  if D % 2 = 0 then 0 else if D % 8 = 1 ∨ D % 8 = 7 then 1 else -1

/-- The supplementary Kronecker value `(D / -1)`: `-1` for negative `D`, and
`1` for nonnegative `D`. In particular, `(0 / -1) = 1`.-/
def _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne (D : ℤ) : ℤ :=
  if D < 0 then -1 else 1

/-- The Kronecker symbol `(D / n)` with natural denominator `n`: the Jacobi symbol
on the odd part of `n` times the supplementary value `(D / 2)` raised to the
`2`-adic valuation of `n`.-/
def _root_.Tengoku.QuadraticNumberFields.kroneckerSymNat (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then
    if D.natAbs = 1 then 1 else 0
  else
    kroneckerTwo D ^ n.factorization 2 * jacobiSym D (n / 2 ^ n.factorization 2)

/-- The Kronecker symbol `(D / n)` with integer denominator `n`, extending
`kroneckerSymNat` by the supplementary factor `(D / -1)` for negative `n`.
The zero-denominator convention is inherited from `kroneckerSymNat`.-/
def _root_.Tengoku.QuadraticNumberFields.kroneckerSym (D n : ℤ) : ℤ :=
  (if n < 0 then kroneckerNegOne D else 1) * kroneckerSymNat D n.natAbs

/-! ### Supplementary and exceptional values -/

/-- The supplementary value `(D / -1)` is `-1` for negative `D`.
@isnad1 id=eq.1h1v.s4.f555700cfdf2 from=translated src=- shape=539d01fc vocab=3f99f41a
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne_of_neg {D : ℤ} (hD : D < 0) :
    kroneckerNegOne D = -1 := by
  simp [kroneckerNegOne, hD]

/-- The supplementary value `(D / -1)` is `1` for nonnegative `D`.
@isnad1 id=eq.1h1v.s4.d9a660148080 from=translated src=- shape=97c35add vocab=3a3ff99b
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne_of_nonneg {D : ℤ} (hD : 0 ≤ D) :
    kroneckerNegOne D = 1 := by
  rw [kroneckerNegOne, ite_eq_right (not_lt.mpr hD)]

/-- The supplementary value `(D / -1)` has square one.
@isnad1 id=eq.0h1v.s4.db8ef97f3213 from=translated src=- shape=98bba06a vocab=d3470522
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne_sq (D : ℤ) : kroneckerNegOne D ^ 2 = 1 := by
  simp [kroneckerNegOne]

/-- The supplementary value `(D / -1)` never vanishes.
@isnad1 id=ne.0h1v.s3.47d318341caa from=translated src=- shape=b14ee516 vocab=2d948d82
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne_ne_zero (D : ℤ) : kroneckerNegOne D ≠ 0 := by
  unfold kroneckerNegOne
  split_ifs <;> norm_num

/-- Away from the exceptional numerator `0`, `(D / -1)` is the integer sign.
@isnad1 id=eq.1h1v.s4.3dc178dcdee1 from=translated src=- shape=cfb0e90d vocab=0b5aaa97
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne_eq_sign_of_ne_zero {D : ℤ} (hD : D ≠ 0) :
    kroneckerNegOne D = D.sign := by
  by_cases hDneg : D < 0
  · rw [kroneckerNegOne_of_neg hDneg,
      Int.sign_eq_neg_one_iff_neg.mpr hDneg]
  · have hDpos : 0 < D :=
      lt_of_le_of_ne (not_lt.mp hDneg) (Ne.symm hD)
    rw [kroneckerNegOne_of_nonneg (le_of_lt hDpos),
      Int.sign_eq_one_iff_pos.mpr hDpos]

/-- The supplementary value `(D / -1)` is multiplicative on nonzero
numerators. The hypotheses exclude the exceptional convention `(0 / -1) = 1`.
@isnad1 id=eq.2h2v.s5.bc2a354d9b75 from=translated src=- shape=eff8b0f5 vocab=c7be52c7
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerNegOne_mul (D E : ℤ) (hD : D ≠ 0) (hE : E ≠ 0) :
    kroneckerNegOne (D * E) = kroneckerNegOne D * kroneckerNegOne E := by
  calc
    kroneckerNegOne (D * E) = (D * E).sign :=
      kroneckerNegOne_eq_sign_of_ne_zero (mul_ne_zero hD hE)
    _ = D.sign * E.sign := Int.sign_mul D E
    _ = kroneckerNegOne D * kroneckerNegOne E := by
      rw [← kroneckerNegOne_eq_sign_of_ne_zero hD,
        ← kroneckerNegOne_eq_sign_of_ne_zero hE]

/-- The natural-denominator Kronecker symbol at denominator `0`.
@isnad1 id=eq.0h1v.s5.7c67eca1d8de from=translated src=- shape=cae85dae vocab=d4fbc173
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSymNat_zero_right (D : ℤ) :
    kroneckerSymNat D 0 = if D.natAbs = 1 then 1 else 0 := by
  simp [kroneckerSymNat]

/-- The natural-denominator Kronecker symbol at denominator `1`.
@isnad1 id=eq.0h1v.s4.7e3332629b00 from=translated src=- shape=0e0c2bda vocab=8776ca92
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSymNat_one_right (D : ℤ) : kroneckerSymNat D 1 = 1 := by
  simp [kroneckerSymNat, kroneckerTwo, jacobiSym.one_right]

/-- The Kronecker symbol at denominator `2` is the supplementary value.
@isnad1 id=eq.0h1v.s3.447abe57b4b2 from=translated src=- shape=cbf5c90a vocab=bf3b61a4
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSymNat_two (D : ℤ) : kroneckerSymNat D 2 = kroneckerTwo D := by
  have h : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  simp [kroneckerSymNat, h]

/-- The supplementary value `(D / 2)` vanishes exactly for even `D`.
@isnad1 id=iff.0h1v.s5.21343d1fdf60 from=translated src=- shape=f6f33501 vocab=67953d73
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerTwo_eq_zero_iff (D : ℤ) : kroneckerTwo D = 0 ↔ D % 2 = 0 := by
  unfold kroneckerTwo
  split_ifs <;> simp_all

/-- The supplementary value `(D / 2)` is `1` exactly for `D ≡ ±1 [ZMOD 8]`.
@isnad1 id=iff.0h1v.s5.67a7c56df57c from=translated src=- shape=77c6f1ce vocab=67953d73
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerTwo_eq_one_iff (D : ℤ) : kroneckerTwo D = 1 ↔ D % 8 = 1 ∨ D % 8 = 7 := by
  unfold kroneckerTwo
  split_ifs <;> simp_all
  omega

/-- The supplementary value `(D / 2)` is `-1` exactly for `D ≡ ±3 [ZMOD 8]`.
@isnad1 id=iff.0h1v.s5.95953cc0af8d from=translated src=- shape=85842a20 vocab=09e40969
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerTwo_eq_neg_one_iff (D : ℤ) :
    kroneckerTwo D = -1 ↔ D % 8 = 3 ∨ D % 8 = 5 := by
  unfold kroneckerTwo
  split_ifs <;> simp_all <;> omega

/-- At a nonnegative integer denominator, `kroneckerSym` reduces to
`kroneckerSymNat` at its absolute value.
@isnad1 id=eq.1h2v.s4.7c46c118c926 from=translated src=- shape=a311ecda vocab=5a5b511e
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_of_nonneg (D : ℤ) {n : ℤ} (hn : 0 ≤ n) :
    kroneckerSym D n = kroneckerSymNat D n.natAbs := by
  rw [kroneckerSym, ite_eq_right (not_lt.mpr hn), one_mul]

/-- At a negative denominator, `kroneckerSym` is the natural-denominator value
times the supplementary factor `(D / -1)`.
@isnad1 id=eq.1h2v.s5.1508f3d16824 from=translated src=- shape=f87f9aa6 vocab=81751336
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_of_neg (D : ℤ) {n : ℤ} (hn : n < 0) :
    kroneckerSym D n = kroneckerNegOne D * kroneckerSymNat D n.natAbs := by
  simp [kroneckerSym, hn]

/-- The integer-denominator Kronecker symbol at denominator `0`.
@isnad1 id=eq.0h1v.s5.8bf1e4048346 from=translated src=- shape=ce6aa856 vocab=745b1cc1
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_zero_right (D : ℤ) :
    kroneckerSym D 0 = if D.natAbs = 1 then 1 else 0 := by
  simp [kroneckerSym]

/-- The integer-denominator Kronecker symbol at denominator `1`.
@isnad1 id=eq.0h1v.s4.23454367f434 from=translated src=- shape=1d838610 vocab=e52570b9
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_one_right (D : ℤ) : kroneckerSym D 1 = 1 := by
  simp [kroneckerSym]

/-- The integer-denominator Kronecker symbol at denominator `-1`.
@isnad1 id=eq.0h1v.s4.06c971bc170e from=translated src=- shape=49af53fb vocab=e1c4d840
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_neg_one_right (D : ℤ) :
    kroneckerSym D (-1) = kroneckerNegOne D := by
  simp [kroneckerSym]

/-- At a natural denominator, the integer-denominator Kronecker symbol agrees with
the natural-denominator interface.
@isnad1 id=eq.0h2v.s3.b8e07d1b0276 from=translated src=- shape=0e70995f vocab=78c1b9e5
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_natCast (D : ℤ) (n : ℕ) :
    kroneckerSym D n = kroneckerSymNat D n := by
  simp [kroneckerSym]

/-- At a negative natural cast, the integer-denominator Kronecker symbol reduces
to `kroneckerSymNat` and the supplementary factor `(D / -1)`.
@isnad1 id=eq.1h2v.s5.9b13d46b18d9 from=translated src=- shape=f4a93f6a vocab=9981aec3
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_neg_natCast (D : ℤ) {n : ℕ} (hn : n ≠ 0) :
    kroneckerSym D (-(n : ℤ)) = kroneckerNegOne D * kroneckerSymNat D n := by
  have hneg : -(n : ℤ) < 0 :=
    neg_neg_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)
  rw [kroneckerSym_of_neg D hneg, Int.natAbs_neg, Int.natAbs_natCast]

/-- The integer-denominator Kronecker symbol at denominator `2`.
@isnad1 id=eq.0h1v.s3.e2a7a6272357 from=translated src=- shape=53eb01b5 vocab=b3475491
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_two_right (D : ℤ) : kroneckerSym D 2 = kroneckerTwo D := by
  change kroneckerSym D ((2 : ℕ) : ℤ) = kroneckerTwo D
  rw [kroneckerSym_natCast, kroneckerSymNat_two]

/-- The integer-denominator Kronecker symbol at denominator `-2`.
@isnad1 id=eq.0h1v.s4.67725c1b46e7 from=translated src=- shape=612320e5 vocab=b28ba0c9
-/
@[simp]
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_neg_two_right (D : ℤ) :
    kroneckerSym D (-2) = kroneckerNegOne D * kroneckerTwo D := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
    kroneckerSym_neg_natCast D (by norm_num), kroneckerSymNat_two]

/-- For an odd prime `p`, the Kronecker symbol `(D / p)` is the Legendre symbol.
@isnad1 id=eq.1h2v.s4.e49419ad2e23 from=translated src=- shape=64f71919 vocab=32ed73e4
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSymNat_eq_legendreSym_of_ne_two (D : ℤ) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) : kroneckerSymNat D p = legendreSym p D := by
  have h2 : p.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp hdvd).symm
  rw [kroneckerSymNat, ite_eq_right hp.out.ne_zero, h2, pow_zero, one_mul, pow_zero, Nat.div_one,
    jacobiSym.legendreSym.to_jacobiSym]

/-- For an odd natural prime viewed as an integer denominator, the Kronecker
symbol `(D / p)` is the Legendre symbol.
@isnad1 id=eq.1h2v.s4.b63b018195c1 from=translated src=- shape=30de81a9 vocab=66078711
-/
theorem _root_.Tengoku.QuadraticNumberFields.kroneckerSym_eq_legendreSym_of_ne_two (D : ℤ) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) : kroneckerSym D (p : ℤ) = legendreSym p D := by
  rw [kroneckerSym_natCast, kroneckerSymNat_eq_legendreSym_of_ne_two D hp2]
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
