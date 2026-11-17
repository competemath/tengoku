import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

theorem Complex.integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance
    (A a b D : ℂ) (hA : 0 < A.re) (hbA : 0 < (b - A).re) (haD : 0 < (a + D - A).re) (hba : 0 < (b - a).re) :
    ∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)
      = Complex.Gamma A * Complex.Gamma (b - A) * Complex.Gamma (a + D - A) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A)) := by exact @_root_.P2MW.S_Complex_integral_Ioi_integral_Ioi_cpow_mul_one_add_cpow_neg_mul_one_add_add_cpow_neg_of_balance.solution A a b D hA hbA haD hba
