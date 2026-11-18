import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.EqHaar
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_TateLocal_modulus_real_eq_nnnorm

open MeasureTheory LanglandsTunnell.TateLocal Metric
open scoped NNReal ENNReal Pointwise

namespace P7Rows
namespace ArchE1

section Complex

end Complex

section Real

/--
@isnad1 id=eq.0h1v.s7.29f5263fcff6 from=translated src=- shape=c6ab00fd vocab=97e265b7
-/
theorem distribHaarChar_real_eq_nnnorm (x : ℝˣ) :
    distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := closedBall 0 1)
    (measure_closedBall_pos volume (0:ℝ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' x.ne_zero, smul_zero, mul_one,
    show ‖(x:ℝ)‖ = ‖(x:ℝ)‖ * 1 by ring,
    Measure.addHaar_closedBall_mul volume (0:ℝ) (norm_nonneg _) zero_le_one,
    Module.finrank_self, pow_one]
  simp only [ofReal_norm, enorm_eq_nnnorm]

/--
@isnad1 id=eq.0h1v.s4.8a927025a1f5 from=translated src=- shape=8ffefcbf vocab=d9239a3c
-/
theorem modulus_real_eq_nnnorm (x : ℝ) : modulus x = ‖x‖₊ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [modulus_of_ne_zero hx, distribHaarChar_real_eq_nnnorm]
    simp

end Real

end P7Rows.ArchE1

/--
@isnad1 id=eq.0h1v.s4.8a927025a1f5 from=translated src=- shape=8ffefcbf vocab=d9239a3c
-/
theorem solution : ∀ (x : ℝ), modulus x = ‖x‖₊ :=
  P7Rows.ArchE1.modulus_real_eq_nnnorm
