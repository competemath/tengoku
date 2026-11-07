/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Data.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real square roots in the complex numbers

This file records the square identity for the complex coercion of a nonnegative
real square root.
-/

namespace Complex

/-- The complex coercion of the real square root of a nonnegative number squares
to that number.
@isnad1 id=eq.1h1v.s5.a0e7f59c1105 from=translated src=- shape=ce55a712 vocab=caa884a4
-/
theorem ofReal_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    (↑(Real.sqrt x) : ℂ) ^ 2 = x := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]

end Complex
