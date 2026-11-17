import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=and.2h2v.s9.843d5904d970 from=translated src=- shape=69be7bc9 vocab=615fc432
-/
theorem MeasureTheory.hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport
    {n : ℕ} (Φ : ℝ × (Fin n → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => deriv (fun t : ℝ => Φ (t, p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × (Fin n → ℝ) => deriv (fun t : ℝ => Φ (t, p.2)) p.1) ∧
    ∀ x : ℝ, HasDerivAt (fun x : ℝ => ∫ y : Fin n → ℝ, Φ (x, y))
      (∫ y : Fin n → ℝ, deriv (fun t : ℝ => Φ (t, y)) x) x := by exact @_root_.P2MW.S_MeasureTheory_hasDerivAt_integral_prod_mk_of_contDiff_of_hasCompactSupport.solution n Φ hΦ hΦc
