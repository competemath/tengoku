import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPowerSeries

/--
@isnad1 id=ex.1h3v.s9.571055920a92 from=translated src=- shape=cfe0b5e3 vocab=1ea1b7af
-/
theorem MvPowerSeries.exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero
    (k : Type*) [CommRing k] (φ : PowerSeries k) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (G : MvPowerSeries (Fin 2) k) :
    ∃ Q : MvPowerSeries (Fin 2) k,
      G = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) * Q +
        MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] G := by exact @_root_.P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero.solution k _ φ hφ0 G
