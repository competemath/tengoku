import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_DrinfeldCurve_LocalChart
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsLocalRing

/--
@isnad1 id=eq.0h2v.s12.2d2d0fd45f26 from=translated src=- shape=9b1a127c vocab=789779fa
-/
theorem DrinfeldCurve.LocalChart.prod_prod_X_sub_C_natCast_mul_add_eq_moore
    (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [CharP R q] :
    ∏ a : Fin q, ∏ b : Fin q,
        (Polynomial.X - Polynomial.C
          (((a : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 1) :
          Polynomial (MvPolynomial (Fin 2) R)) =
      Polynomial.X ^ (q ^ 2)
        - Polynomial.C (∑ i ∈ Finset.range (q + 1),
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
          Polynomial.X ^ q
        + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) R) * MvPolynomial.X 1 ^ q
            - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore.solution q _ R _ _
