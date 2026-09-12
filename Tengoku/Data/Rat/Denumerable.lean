/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Tengoku.Algebra.Ring.Rat
public import Tengoku.Data.Rat.Encodable
public import Tengoku.Algebra.CharZero.Infinite
public import Tengoku.Logic.Denumerable

/-!
# Denumerability of ℚ

This file proves that ℚ is denumerable.

The fact that ℚ has cardinality ℵ₀ is proved in `Mathlib/Data/Rat/Cardinal.lean`
-/

public section

assert_not_exists Module Field

namespace Rat

open Denumerable

/-- **Denumerability of the Rational Numbers** -/
instance instDenumerable : Denumerable ℚ := ofEncodableOfInfinite ℚ

end Rat
