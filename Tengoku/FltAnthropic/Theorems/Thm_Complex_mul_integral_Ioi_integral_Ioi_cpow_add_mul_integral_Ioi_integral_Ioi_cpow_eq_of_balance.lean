import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MeasureTheory Set

/--
@isnad1 id=eq.6h4v.s9.2496d6e5ee77 from=translated src=- shape=b727984f vocab=6c137a83
-/
theorem Complex.mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance
    (A a b D : ℂ) (hA : 0 < A.re) (ha : 0 < a.re) (hD : 0 < D.re) (hba : 0 < (b - a).re)
    (hbA : 0 < (b - A + 1).re) (haD : 0 < (a + D - A + 1).re) :
    a * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-(a + 1)) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-D)) +
    D * (∫ x in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ),
        (x : ℂ) ^ (A - 1) * ((1 + x : ℝ) : ℂ) ^ (-a) *
          ((y : ℂ) ^ (a + D - 1) * ((1 + y : ℝ) : ℂ) ^ (-b)) * ((1 + x + y : ℝ) : ℂ) ^ (-(D + 1)))
      = Complex.Gamma A * Complex.Gamma (b - A + 1) * Complex.Gamma (a + D - A + 1) * Complex.Gamma (b - a) /
          (Complex.Gamma b * Complex.Gamma (D + b - A + 1)) := by exact @_root_.P2MW.S_Complex_mul_integral_Ioi_integral_Ioi_cpow_add_mul_integral_Ioi_integral_Ioi_cpow_eq_of_balance.solution A a b D hA ha hD hba hbA haD
