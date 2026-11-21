import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false
open ModularCurve
/--
@isnad1 id=ex.3h4v.s9.b8d87babdb30 from=translated src=- shape=17a25465 vocab=82bb5478
-/
theorem ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] (φ : R →+* K) (hφ : Function.Injective φ)
    (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y := by exact @_root_.P2MW.S_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective.solution R _ _ _ K _ φ hφ y hy hint
