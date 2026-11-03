/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Zsqrtd.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Half-Integer Representatives

This file defines half-integer representatives `(a + b√d) / 2` in quadratic fields
and provides basic structural lemmas. These are used in the classification of
rings of integers when `d ≡ 1 (mod 4)`.

## Main Definitions

* `halfInt d a' b'`: The half-integer `(a' + b'√d) / 2` in `Q(√d)`.
* `omegaHalf d`: The distinguished generator `(1 + √d) / 2`.

## Main Theorems

* `halfInt_re`, `halfInt_im`: Coordinate simp lemmas.
* `omegaHalf_re`, `omegaHalf_im`: Coordinates of `omegaHalf`.
* `trace_halfInt`: Trace of `halfInt d a' b'` is `a'`.
* `norm_halfInt`: Norm of `halfInt d a' b'` is `(a'² - d·b'²) / 4`.
-/

local notation "ℚ√" d => Qsqrtd d

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- Canonical half-integer representative `(a' + b'√d)/2` in `Q(√d)`.-/
abbrev halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  Zsqrtd.halfInt (d := d) a' b'

/-- The distinguished half-integer generator `(1 + √d)/2`.-/
abbrev omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1

/--
@isnad1 id=eq.0h3v.s5.53dfdb2378a3 from=translated src=- shape=17b77b7e vocab=f378643c
-/
@[simp] theorem halfInt_re (d a' b' : ℤ) :
    (halfInt d a' b').re = (a' : ℚ) / 2 := rfl

/--
@isnad1 id=eq.0h3v.s5.cd229ea7c32f from=translated src=- shape=325e86bb vocab=2b580d22
-/
@[simp] theorem halfInt_im (d a' b' : ℤ) :
    (halfInt d a' b').im = (b' : ℚ) / 2 := rfl

/--
@isnad1 id=eq.0h1v.s5.5bdc5b2f1b91 from=translated src=- shape=ba8e632d vocab=5b54ebc9
-/
@[simp] theorem omegaHalf_re (d : ℤ) :
    (omegaHalf d).re = (1 : ℚ) / 2 := rfl

/--
@isnad1 id=eq.0h1v.s5.1ed57a6930f5 from=translated src=- shape=ba8e632d vocab=e2aaca5c
-/
@[simp] theorem omegaHalf_im (d : ℤ) :
    (omegaHalf d).im = (1 : ℚ) / 2 := rfl

/-- Trace of `halfInt` is `a'`.
@isnad1 id=eq.0h3v.s8.6f1e682f2bbb from=translated src=- shape=0a702ccc vocab=aa1dafdc
-/
theorem trace_halfInt (d a' b' : ℤ) : Algebra.trace ℚ (Qsqrtd d) (halfInt d a' b') = a' := by
  -- The trace on `Q(√d)` is twice the real part, so for `(a' + b'√d)/2`
  -- the denominator cancels and leaves `a'`.
  simp [halfInt]

/-- Norm of `halfInt` is `(a'² - d*b'²)/4`.
@isnad1 id=eq.0h3v.s6.74924cf51ee3 from=translated src=- shape=d94420cd vocab=6804ee9f
-/
theorem norm_halfInt (d a' b' : ℤ) :
    Qsqrtd.norm (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  -- Expand `re = a'/2` and `im = b'/2` in the formula
  -- `N(r + s√d) = r² - d s²`.
  simp [halfInt, Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

end RingOfIntegers
end QuadraticNumberFields
