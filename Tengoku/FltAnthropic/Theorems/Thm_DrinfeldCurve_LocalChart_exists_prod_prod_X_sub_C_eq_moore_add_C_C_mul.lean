import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing
attribute [-simp] DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq

set_option autoImplicit false

open IsLocalRing Polynomial

/--
@isnad1 id=ex.2h3v.s12.5dda82c0e96b from=translated src=- shape=62601ac8 vocab=267e556d
-/
theorem DrinfeldCurve.LocalChart.exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (hq : (q : W) ∈ maximalIdeal W) :
    ∃ E : Polynomial (MvPolynomial (Fin 2) W),
      ∏ a : Fin q, ∏ b : Fin q,
          (Polynomial.X - Polynomial.C
            (((a : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 1) :
            Polynomial (MvPolynomial (Fin 2) W)) =
        Polynomial.X ^ (q ^ 2)
          - Polynomial.C (∑ i ∈ Finset.range (q + 1),
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) W) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
            Polynomial.X ^ q
          + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) W) * MvPolynomial.X 1 ^ q
              - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X
          + Polynomial.C (MvPolynomial.C π) * E := by exact @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul.solution q _ W _ _ π hπ hq
