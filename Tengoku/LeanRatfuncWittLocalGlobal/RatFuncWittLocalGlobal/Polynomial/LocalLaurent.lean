/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.LaurentPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebra of local Laurent leading coefficients

Dimension-independent rules for multiplication, negation, ordinary non-root
values, and normalized linear factors.
-/

namespace RatFuncWittLocalGlobal

open _root_.Polynomial

universe u

noncomputable section

/-- The leading coefficient after substituting the local Laurent parameter
at a real center into a polynomial.-/
def localLaurentLeadingCoeff
    {R : Type u} [Field R] (r ε : R) (p : Polynomial R) : R :=
  (algebraMap (Polynomial R) (LaurentSeries R)
    (p.comp (C ε * X + C r))).leadingCoeff

/-- Local Laurent leading coefficients are multiplicative.
@isnad1 id=eq.0h5v.s6.82a873294a2c from=translated src=- shape=77fe1fda vocab=30b18d52
-/
theorem localLaurentLeadingCoeff_mul
    {R : Type u} [Field R]
    (r ε : R) (p q : Polynomial R) :
    localLaurentLeadingCoeff r ε (p * q) =
      localLaurentLeadingCoeff r ε p *
        localLaurentLeadingCoeff r ε q := by
  simp [localLaurentLeadingCoeff, HahnSeries.leadingCoeff_mul]

/-- At a point where a polynomial does not vanish, the local Laurent leading
coefficient is its ordinary value.
@isnad1 id=eq.1h4v.s6.c58fa9d0251c from=translated src=- shape=cf9e44d7 vocab=9d547e15
-/
theorem localLaurentLeadingCoeff_eq_eval_of_ne_zero
    {R : Type u} [Field R]
    {r ε : R} {p : Polynomial R} (hp : p.eval r ≠ 0) :
    localLaurentLeadingCoeff r ε p = p.eval r := by
  exact RatFunc.scaledShiftedPolynomial_laurentSeries_leadingCoeff hp

/-- The normalized linear factor has local Laurent leading coefficient equal
to the orientation scalar.
@isnad1 id=eq.0h3v.s7.85c9757091aa from=translated src=- shape=179253d5 vocab=8af3b8c2
-/
theorem localLaurentLeadingCoeff_X_sub_C
    {R : Type u} [Field R] (r ε : R) :
    localLaurentLeadingCoeff r ε (X - C r) = ε := by
  unfold localLaurentLeadingCoeff
  rw [show ((X - C r : Polynomial R).comp (C ε * X + C r)) = C ε * X by
    simp [Polynomial.sub_comp]]
  exact RatFunc.powerSeries_C_mul_X_laurentSeries_leadingCoeff ε

end

end RatFuncWittLocalGlobal
