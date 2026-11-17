import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open MeasureTheory

theorem _root_.Tengoku.FltAnthropic.contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (j : ℕ) (x : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) ∧
    ∀ (N : ℕ) (y : Fin n → ℝ),
      ‖iteratedFDeriv ℝ N (fun y' : Fin n → ℝ => iteratedDeriv j (fun t : ℝ => Φ (t, y')) x) y‖ ≤
        ‖iteratedFDeriv ℝ (N + j) Φ (x, y)‖ := by exact @_root_.P2MW.S_contDiff_iteratedDeriv_slice_and_norm_iteratedFDeriv_le_norm_iteratedFDeriv_add.solution n Φ hΦ j x
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
