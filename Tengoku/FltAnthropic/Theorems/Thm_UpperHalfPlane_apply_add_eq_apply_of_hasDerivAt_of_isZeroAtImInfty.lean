import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Manifold Topology

theorem UpperHalfPlane.apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty {h : ℝ} (hh : 0 < h)
    {g : UpperHalfPlane → ℂ} (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) h)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hzero : UpperHalfPlane.IsZeroAtImInfty g)
    {φ : ℂ → ℂ} (hφ : ∀ τ : UpperHalfPlane, HasDerivAt φ (g τ) ↑τ) (τ : UpperHalfPlane) :
    φ (↑τ + h) = φ ↑τ := by exact @_root_.P2MW.S_UpperHalfPlane_apply_add_eq_apply_of_hasDerivAt_of_isZeroAtImInfty.solution h hh g hper hhol hzero φ hφ τ
