import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem PowerSeries.existsUnique_algHom_apply_X_eq_of_isNilpotent
    {A : Type} [CommRing A] {T : Type} [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) :
    (∃! φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t) ∧
    (∀ φ : PowerSeries A →ₐ[A] T, φ PowerSeries.X = t → ∀ N : ℕ, t ^ N = 0 →
      ∀ f : PowerSeries A, φ f = ∑ i ∈ Finset.range N, algebraMap A T (PowerSeries.coeff i f) * t ^ i) := by exact @_root_.P2MW.S_PowerSeries_existsUnique_algHom_apply_X_eq_of_isNilpotent.solution A _ T _ _ t ht
