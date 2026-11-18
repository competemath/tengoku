import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel
/--
@isnad1 id=ex.3h4v.s10.1ba8a9b2c5a2 from=translated src=- shape=98dd3c26 vocab=7e9385b6
-/
theorem ModularCurve.UVCrossingModel.exists_mk_eq_mk_expand_of_dvd_sub
    {W : Type*} [CommRing W] (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (e : ℕ) (he : e ≠ 0)
    (F : MvPowerSeries (Fin 2) W)
    (hF : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F ≠ 0 → (e : ℤ) ∣ (d 0 : ℤ) - d 1) :
    ∃ G : MvPowerSeries (Fin 2) W, mk π F = mk π (MvPowerSeries.expand e he G) := by exact @_root_.P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub.solution W _ π _ hsep e he F hF
