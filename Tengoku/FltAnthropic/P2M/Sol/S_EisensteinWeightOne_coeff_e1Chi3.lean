import Tengoku.Seed.RingTheory.PowerSeries.Basic
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_EisensteinWeightOne_coeff_e1Chi3.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_EisensteinWeightOne_coeff_e1Chi3

open EisensteinWeightOne

/--
@isnad1 id=eq.0h1v.s6.5ce33dc245fc from=translated src=- shape=47159a6a vocab=cbd60f3d
-/
theorem solution (n : ℕ) :
    PowerSeries.coeff n e1Chi3 = if n = 0 then 1 else 6 * sigmaChi n := by
  rw [e1Chi3, PowerSeries.coeff_mk]
