import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The arithmetic combining the colored and full-graph covers. -/

namespace Tuza

/-- Arithmetic in the first colored-cover comparison, with denominators cleared.
@isnad1 id=le.3h5v.s7.14841cc7bc83 from=translated src=- shape=e0040f7b vocab=ebd7a482
-/
theorem colored_bound_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hsecond : t + r ≤ 2 * p + 3 * a) (hra : r ≤ a) :
    3 * t + 2 * u ≤ 8 * p := by
  omega

/-- Arithmetic after applying the first colored estimate to the residual family.
@isnad1 id=le.2h5v.s7.2a5ed005fd0c from=translated src=- shape=bd9d447e vocab=ebd7a482
-/
theorem colored_refined_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hresidual : 3 * t + 2 * r ≤ 6 * p + 8 * a) :
    4 * t + u ≤ 9 * p + 6 * a := by
  omega

/-- Equations (3)--(6), combined with weights 20, 8, 19, and 12.
@isnad1 id=le.4h7v.s8.57cdd85d59c8 from=translated src=- shape=846b0ff5 vocab=ebd7a482
-/
theorem four_bounds_arithmetic {t n a b c d h : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 8 * t + 8 * c ≤ 12 * n + 20 * a + 12 * b + 3 * h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolored : 4 * t + 4 * b + h ≤ 12 * n + 9 * c + 6 * d) :
    59 * t + d ≤ 165 * n := by
  omega

end Tuza
