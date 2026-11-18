import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (μ : Measure G) [μ.IsHaarMeasure] (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w₁ w₂ : G → ℝ)
    (hw₁ : (∀ x, 0 ≤ w₁ x) ∧ Measurable w₁ ∧ HasCompactSupport w₁ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₁ ((t : G) * x) ∂τ = 1)
    (hw₂ : (∀ x, 0 ≤ w₂ x) ∧ Measurable w₂ ∧ HasCompactSupport w₂ ∧
      ∀ x, F x ≠ 0 → ∫ t : T, w₂ ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w₁ x : ℂ) ∂μ = ∫ x, F x * (w₂ x : ℂ) ∂μ := by exact @_root_.P2MW.S_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one.solution G _ _ _ _ _ _ _ T hT _ _ μ _ τ _ _ F hFm hFb hFT w₁ w₂ hw₁ hw₂
