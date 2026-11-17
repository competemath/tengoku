import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold

theorem UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic {h : ℝ} (hh : 0 < h) {u v : UpperHalfPlane → ℂ}
    (hu_per : Function.Periodic (u ∘ UpperHalfPlane.ofComplex) h) (hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hu_bdd : UpperHalfPlane.IsBoundedAtImInfty u)
    (hv : ∀ τ : UpperHalfPlane, HasDerivAt (v ∘ UpperHalfPlane.ofComplex) (u τ) ↑τ)
    (hv_per : Function.Periodic (v ∘ UpperHalfPlane.ofComplex) h) :
    UpperHalfPlane.IsBoundedAtImInfty v := by exact @_root_.P2MW.S_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.solution h hh u v hu_per hu_hol hu_bdd hv hv_per
