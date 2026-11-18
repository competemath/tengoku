import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_modulus_complex_eq_nnnorm_sq

open MeasureTheory LanglandsTunnell.TateLocal Metric
open scoped NNReal ENNReal Pointwise

namespace P7Rows
namespace ArchE1

section Complex

/--
@isnad1 id=eq.0h1v.s7.837a47f93272 from=translated src=- shape=6a35519f vocab=70016a1b
-/
theorem distribHaarChar_complex_eq_nnnorm_sq (z : ℂˣ) :
    distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := closedBall 0 1)
    (measure_closedBall_pos volume (0:ℂ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' z.ne_zero, smul_zero, mul_one,
    show ‖(z:ℂ)‖ = ‖(z:ℂ)‖ * 1 by ring,
    Measure.addHaar_closedBall_mul volume (0:ℂ) (norm_nonneg _) zero_le_one,
    Complex.finrank_real_complex]
  simp [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_nnnorm]

/--
@isnad1 id=eq.0h1v.s5.598a0775c5a3 from=translated src=- shape=2c770a6d vocab=6ed685d0
-/
theorem modulus_complex_eq_nnnorm_sq (z : ℂ) : modulus z = ‖z‖₊ ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

end Complex

section Real

end Real

end P7Rows.ArchE1

/--
@isnad1 id=eq.0h1v.s5.598a0775c5a3 from=translated src=- shape=2c770a6d vocab=6ed685d0
-/
theorem solution : ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 :=
  P7Rows.ArchE1.modulus_complex_eq_nnnorm_sq
