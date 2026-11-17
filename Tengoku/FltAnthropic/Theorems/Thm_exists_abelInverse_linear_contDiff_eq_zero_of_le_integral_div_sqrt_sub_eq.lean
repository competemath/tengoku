import Tengoku.Seed.Analysis.Calculus.ContDiff.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Set
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Basic
import Tengoku.Seed.Data.Real.Sqrt
import Tengoku.FltAnthropic.P2M.Sol.S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=ex.0h1v.s8.2796bd9ae5a9 from=translated src=- shape=2cd9a5a3 vocab=ec97eb06
-/
theorem _root_.Tengoku.FltAnthropic.exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    ∃ T : (ℝ → ℂ) → (ℝ → ℂ),
      (∀ f g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ContDiff ℝ (⊤ : ℕ∞) g →
        HasCompactSupport g → ∀ a b : ℂ, T (fun ξ => a * f ξ + b * g ξ) = fun ξ => a * T f ξ + b * T g ξ) ∧
      ∀ G : ℝ × P → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
        ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => T (fun ξ => G (ξ, q.2)) q.1) ∧
        (∀ R : ℝ, (∀ (p : P) (ξ : ℝ), R ≤ ξ → G (ξ, p) = 0) →
          ∀ (p : P) (ξ : ℝ), R ≤ ξ → T (fun ξ' => G (ξ', p)) ξ = 0) ∧
        ∀ (η : ℝ) (p : P),
          ∫ ξ in Set.Ioi η, T (fun ξ' => G (ξ', p)) ξ / ((Real.sqrt (ξ - η) : ℝ) : ℂ) = G (η, p) := by exact @_root_.P2MW.S_exists_abelInverse_linear_contDiff_eq_zero_of_le_integral_div_sqrt_sub_eq.solution P _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
