import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_algEquiv_apply_X_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_algEquiv_apply_X_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPowerSeries
theorem MvPowerSeries.exists_algEquiv_apply_X_eq
    {W : Type*} [CommRing W] (f : Fin 2 → MvPowerSeries (Fin 2) W)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (f i) = 0)
    (h1 : IsUnit (Matrix.det (Matrix.of fun i j : Fin 2 => MvPowerSeries.coeff (Finsupp.single j 1) (f i)))) :
    ∃ e : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W, ∀ i, e (MvPowerSeries.X i) = f i := by exact @_root_.P2MW.S_MvPowerSeries_exists_algEquiv_apply_X_eq.solution W _ f h0 h1
