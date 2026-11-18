import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem PartialDeriv.contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single
    (n m : ℕ) (f : (Fin n → ℝ) → ℂ) (g : Fin n → (Fin n → ℝ) → ℂ)
    (hg : ∀ j, ContDiff ℝ m (g j))
    (hfg : ∀ (t : Fin n → ℝ) (j : Fin n),
      HasDerivAt (fun s : ℝ => f (t + s • (Pi.single j (1 : ℝ) : Fin n → ℝ))) (g j t) 0) :
    ContDiff ℝ (m + 1) f ∧
      (∀ t, HasFDerivAt f (∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (g j t)) t) ∧
      ∀ k, k ≤ m → ∀ t, ‖iteratedFDeriv ℝ (k + 1) f t‖ ≤ ∑ j, ‖iteratedFDeriv ℝ k (g j) t‖ := by exact @_root_.P2MW.S_PartialDeriv_contDiff_succ_and_norm_iteratedFDeriv_le_of_hasDerivAt_single.solution n m f g hg hfg
