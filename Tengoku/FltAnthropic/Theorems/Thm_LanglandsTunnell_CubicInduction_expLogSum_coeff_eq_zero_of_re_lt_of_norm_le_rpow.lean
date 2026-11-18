import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.FltAnthropic.P2M.Sol.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=eq.5h8v.s8.939f3880b357 from=translated src=- shape=ce9c49c5 vocab=a23a55e7
-/
theorem
LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    {ι : Type*} [Fintype ι] (e : ι → ℂ) (j : ι → ℕ) (c : ι → ℂ)
    (hinj : Function.Injective fun i => (e i, j i))
    (θ₀ : ℝ) (F R : ℝ → ℂ)
    (hF : ∀ y : ℝ, 0 < y → y ≤ 1 → F y = ∑ i, c i * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) + R y)
    (hR : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖R y‖ ≤ K * y ^ θ₀)
    (hray : ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖F y₁‖ ≤ C * y₁ ^ θ₀) :
    ∀ i, (e i).re < θ₀ → c i = 0 := by exact @_root_.P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow.solution ι _ e j c hinj θ₀ F R hF hR hray
