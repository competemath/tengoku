import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=eq.9h7v.s9.25afcbdf74f1 from=translated src=- shape=d954a54c vocab=fd8ed375
-/
theorem AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
    {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup G) [MeasurableSpace T] [MeasurableInv T]
    (hT : Measurable (Subtype.val : T → G))
    (τ : Measure T) [SFinite τ] [τ.IsInvInvariant]
    (F : G → ℂ) (hF : Measurable F) (hFT : ∀ (t : T) (x : G), F ((t : G) * x) = F x)
    (w w' : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw' : ∀ x, 0 ≤ w' x)
    (hwm : Measurable w) (hw'm : Measurable w')
    (h1 : ∀ x, F x ≠ 0 → ∫ t : T, w ((t : G) * x) ∂τ = 1)
    (h1' : ∀ x, F x ≠ 0 → ∫ t : T, w' ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (w x : ℂ) ∂μ = ∫ x, F x * (w' x : ℂ) ∂μ := by exact @_root_.P2MW.S_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one.solution G _ _ _ μ _ _ T _ _ hT τ _ _ F hF hFT w w' hw hw' hwm hw'm h1 h1'
