import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.1h3v.s11.ae1173dc4581 from=translated src=- shape=0b69d394 vocab=49ae6608
-/
theorem MvPowerSeries.exists_basis_ker_linearCombination_of_ne_zero
    {κ : Type} [Field κ] {m : ℕ} (f : Fin m → MvPowerSeries (Fin 2) κ) (hf : f ≠ 0) :
    ∃ (r : ℕ) (e : Module.Basis (Fin r) (MvPowerSeries (Fin 2) κ)
        (LinearMap.ker (Fintype.linearCombination (MvPowerSeries (Fin 2) κ) f))), r + 1 = m := by exact @_root_.P2MW.S_MvPowerSeries_exists_basis_ker_linearCombination_of_ne_zero.solution κ _ m f hf
