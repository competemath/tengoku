import Tengoku.Seed.Analysis.Calculus.ContDiff.Basic
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

/--
@isnad1 id=ex.0h1v.s9.8f52414d09d8 from=translated src=- shape=04500550 vocab=431a9125
-/
theorem _root_.Tengoku.FltAnthropic.exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ W : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, W (fun x => a * f x + b * g x) = fun x => a * W f x + b * W g x) ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ContDiff ℝ (⊤ : ℕ∞) (W f) ∧ HasCompactSupport (W f) ∧
        ((∀ x : ℝ, f (-x) = f x) → ∀ x : ℝ, W f (x ^ 2) = f x) ∧
        ((∀ x : ℝ, f (-x) = -f x) → ∀ x : ℝ, (x : ℂ) * W f (x ^ 2) = f x)) ∧
      ∀ H : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) H → HasCompactSupport H →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) ∧
          HasCompactSupport (fun q : ℝ × P => W (fun x => H (x, q.2)) q.1) := by exact @_root_.P2MW.S_exists_linear_contDiff_hasCompactSupport_apply_sq_eq_of_even_of_odd.solution P _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
