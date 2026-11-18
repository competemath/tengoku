import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory FourierTransform

/--
@isnad1 id=and.3h3v.s8.2e1fdadc6ebe from=translated src=- shape=b7053eaf vocab=8a8b4baa
-/
theorem LocalParametrix.continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (r : V → ℂ) (hr : ContDiff ℝ (⊤ : ℕ∞) r) (s : ℝ) (hs : (Module.finrank ℝ V : ℝ) < s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(s + n))) :
    Continuous (𝓕 r) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (𝓕 r) {0}ᶜ := by exact @_root_.P2MW.S_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le.solution V _ _ _ _ _ r hr s hs hb
