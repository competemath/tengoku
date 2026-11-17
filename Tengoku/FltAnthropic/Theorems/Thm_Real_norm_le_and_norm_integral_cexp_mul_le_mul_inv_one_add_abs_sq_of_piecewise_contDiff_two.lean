import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory

/--
@isnad1 id=and.10h7v.s9.91db1d6ec3a6 from=translated src=- shape=ba1781b2 vocab=b5bf9b25
-/
theorem Real.norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two
    (g gm gp : ℝ → ℂ) (R M₀ M₂ J : ℝ) (hR : 0 ≤ R)
    (hgm : ContDiff ℝ 2 gm) (hgp : ContDiff ℝ 2 gp)
    (hm : ∀ x, x ≤ 0 → g x = gm x) (hp : ∀ x, 0 ≤ x → g x = gp x)
    (hsupp : ∀ x, R < |x| → g x = 0)
    (hM₀ : ∀ x, ‖g x‖ ≤ M₀)
    (hM₂m : ∀ x, x ≤ 0 → ‖iteratedDeriv 2 gm x‖ ≤ M₂)
    (hM₂p : ∀ x, 0 ≤ x → ‖iteratedDeriv 2 gp x‖ ≤ M₂)
    (hJ : ‖deriv gp 0 - deriv gm 0‖ ≤ J) :
    (∀ x : ℝ, ‖g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |x|)⁻¹ ^ 2) ∧
    (∀ ξ : ℝ, ‖∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * x : ℝ) : ℂ))) * g x‖ ≤
        (M₀ * (1 + R) ^ 2 + 8 * R * M₀ + (2 * R * M₂ + J) / Real.pi ^ 2) * (1 + |ξ|)⁻¹ ^ 2) := by exact @_root_.P2MW.S_Real_norm_le_and_norm_integral_cexp_mul_le_mul_inv_one_add_abs_sq_of_piecewise_contDiff_two.solution g gm gp R M₀ M₂ J hR hgm hgp hm hp hsupp hM₀ hM₂m hM₂p hJ
