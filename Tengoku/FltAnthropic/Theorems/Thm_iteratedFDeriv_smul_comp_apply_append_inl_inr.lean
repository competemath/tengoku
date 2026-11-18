import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_iteratedFDeriv_smul_comp_apply_append_inl_inr

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_iteratedFDeriv_smul_comp_apply_append_inl_inr.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

theorem _root_.Tengoku.FltAnthropic.iteratedFDeriv_smul_comp_apply_append_inl_inr
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (A : E → F) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j l : ℕ) (e : E) (ρ : ℝ) (u : Fin j → E) :
    iteratedFDeriv ℝ (j + l) (fun p : E × ℝ => φ p.2 • A p.1) (e, ρ)
        (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ((0, 1) : E × ℝ))) =
      iteratedDeriv l φ ρ • iteratedFDeriv ℝ j A e u := by exact @_root_.P2MW.S_iteratedFDeriv_smul_comp_apply_append_inl_inr.solution E _ _ F _ _ φ hφ A hA j l e ρ u
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
