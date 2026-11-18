import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=eq.5h10v.s8.48d0e66c07be from=translated src=- shape=56d4b357 vocab=1ed8555d
-/
theorem MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
    {T : Type*} [MeasurableSpace T] (μ : Measure T) (d : T → ℤ) (hd : Measurable d)
    (g : T → ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hg : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b → Integrable (fun t => g t * Y ^ d t) μ)
    (Q P : Polynomial ℂ) (n : ℤ)
    (hfe : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b →
      (∫ t, g t * Y ^ d t ∂μ) * Q.eval Y = P.eval Y * Y ^ n)
    (j : ℤ) :
    ∑ i ∈ Q.support, Q.coeff i * ∫ t in d ⁻¹' {j - (i : ℤ)}, g t ∂μ =
      if n ≤ j then P.coeff (j - n).toNat else 0 := by exact @_root_.P2MW.S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq.solution T _ μ d hd g a b ha hab hg Q P n hfe j
