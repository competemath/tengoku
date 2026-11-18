import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open MvPowerSeries

/--
@isnad1 id=ex.2h3v.s8.c9719abe24c1 from=translated src=- shape=29846bc6 vocab=570a1e29
-/
theorem MvPowerSeries.exists_eq_X_sub_subst_mul_of_subst_eq_zero
    {R : Type u} [CommRing R] (f : MvPowerSeries (Fin 2) R)
    (φ : PowerSeries R) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (hroot : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), φ] f = 0) :
    ∃ M : MvPowerSeries (Fin 2) R,
      f = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) φ) * M := by exact @_root_.P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero.solution R _ f φ hφ0 hroot
