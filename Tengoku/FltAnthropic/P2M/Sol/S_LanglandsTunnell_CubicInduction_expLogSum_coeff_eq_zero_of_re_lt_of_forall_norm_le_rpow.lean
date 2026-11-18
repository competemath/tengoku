import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.FltAnthropic.Theorems.Thm_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_forall_norm_le_rpow

set_option autoImplicit false

theorem solution
    {ι : Type*} [Fintype ι] {P : Type*} (e : ι → ℂ) (j : ι → ℕ) (c : ι → P → ℂ)
    (hinj : Function.Injective fun i => (e i, j i))
    (θ₀ : ℝ) (F R : ℝ → P → ℂ)
    (hF : ∀ p : P, ∀ y : ℝ, 0 < y → y ≤ 1 → F y p = ∑ i, c i p * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) + R y p)
    (hR : ∀ p : P, ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖R y p‖ ≤ K * y ^ θ₀)
    (hray : ∀ p : P, ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖F y₁ p‖ ≤ C * y₁ ^ θ₀) :
    ∀ i, (e i).re < θ₀ → c i = 0 := by
  intro i hi
  funext p
  exact LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow e j (fun k => c k p)
    hinj θ₀ (fun y => F y p) (fun y => R y p) (hF p) (hR p) (hray p) i hi
