import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LaurentSeries_coeff_pow_char

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LaurentSeries_coeff_pow_char.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_pow_char {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q]
    (f : LaurentSeries R) (n : ℤ) :
    (f ^ q).coeff n = if (q : ℤ) ∣ n then f.coeff (n / q) ^ q else 0 := by exact @_root_.P2MW.S_LaurentSeries_coeff_pow_char.solution R _ q _ _ f n
