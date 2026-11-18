import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ} (e : Fin n → X → ℂ)
    (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (w : X → ℂ) (hw : Integrable (fun x => ‖w x‖ ^ 2) μ)
    (hwe : ∀ j, Integrable (fun x => w x * conj (e j x)) μ) :
    ∑ j, ‖∫ x, w x * conj (e j x) ∂μ‖ ^ 2 ≤ ∫ x, ‖w x‖ ^ 2 ∂μ := by exact @_root_.P2MW.S_MeasureTheory_sum_norm_sq_integral_mul_conj_le_integral_norm_sq_of_orthonormal.solution X _ μ n e hint hon w hw hwe
