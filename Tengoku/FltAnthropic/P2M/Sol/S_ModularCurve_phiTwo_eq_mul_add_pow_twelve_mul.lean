import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ClassicalModularPolynomials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_phiTwo_eq_mul_add_pow_twelve_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_phiTwo_eq_mul_add_pow_twelve_mul

set_option autoImplicit false
set_option maxHeartbeats 16000000

open Polynomial ModularCurve

theorem solution :
    phiTwo
      = ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2 + 2608 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) + 768 - (X : Polynomial (Polynomial ℤ))) * ((C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) - (X : Polynomial (Polynomial ℤ)) ^ 2 + 1488 * (X : Polynomial (Polynomial ℤ)) + 3328)
        + 2 ^ 12 * ((-38443359999 + 2133623 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) - 41 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ)) ^ 2)
                    + (2135464 + 9007 * (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ))) * (X : Polynomial (Polynomial ℤ)) + (-39 + (C (X : Polynomial ℤ) : Polynomial (Polynomial ℤ))) * (X : Polynomial (Polynomial ℤ)) ^ 2) := by
  simp only [phiTwo, phiTwoC2, phiTwoC1, phiTwoC0, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat]
  ring
