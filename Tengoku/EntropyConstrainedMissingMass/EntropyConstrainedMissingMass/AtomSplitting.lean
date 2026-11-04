import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Probability
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.ObjectiveCalculus
import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.Support

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Splitting into an unused coordinate: genuine ℓ¹ perturbations of probability vectors. -/

namespace EntropyConstrainedMissingMass

noncomputable section
open Set Filter
open scoped Topology ENNReal

/-- The real entropy gained by replacing mass `a` by `a-ε` and `ε`.-/
def splitEntropyIncrement (a ε : ℝ) : ℝ :=
  Real.negMulLog (a - ε) + Real.negMulLog ε - Real.negMulLog a

theorem continuous_splitEntropyIncrement (a : ℝ) : Continuous (splitEntropyIncrement a) := by
  unfold splitEntropyIncrement
  fun_prop

@[simp] theorem splitEntropyIncrement_zero (a : ℝ) : splitEntropyIncrement a 0 = 0 := by
  simp [splitEntropyIncrement]

theorem tendsto_splitEntropyIncrement_zero (a : ℝ) :
    Tendsto (splitEntropyIncrement a) (𝓝 0) (𝓝 0) := by
  simpa only [splitEntropyIncrement_zero] using (continuous_splitEntropyIncrement a).tendsto 0

theorem splitEntropyIncrement_pos {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) :
    0 < splitEntropyIncrement a ε := by
  have hleft : 0 < a - ε := sub_pos.mpr hεa
  have hl1 : 0 < Real.log a - Real.log (a - ε) :=
    sub_pos.mpr (Real.log_lt_log hleft (by linarith))
  have hl2 : 0 < Real.log a - Real.log ε :=
    sub_pos.mpr (Real.log_lt_log hε hεa)
  have heq : splitEntropyIncrement a ε =
      (a - ε) * (Real.log a - Real.log (a - ε)) + ε * (Real.log a - Real.log ε) := by
    simp only [splitEntropyIncrement, Real.negMulLog]
    ring
  rw [heq]
  exact add_pos (mul_pos hleft hl1) (mul_pos hε hl2)

namespace ProbabilityVector
variable {ι : Type*}

/-- Subtract from coordinate `i` and put the removed mass at coordinate `j`.-/
def splitCoord (p : ProbabilityVector ι) (i j : ι) (ε : ℝ) : ι → ℝ := by
  classical
  exact Function.update (Function.update p.coord i (p.coord i - ε)) j ε

theorem splitCoord_i (p : ProbabilityVector ι) {i j : ι} (hij : i ≠ j) (ε : ℝ) :
    splitCoord p i j ε i = p.coord i - ε := by
  classical
  simp [splitCoord, hij]

@[simp] theorem splitCoord_j (p : ProbabilityVector ι) (i j : ι) (ε : ℝ) :
    splitCoord p i j ε j = ε := by
  classical
  simp [splitCoord]

theorem splitCoord_other (p : ProbabilityVector ι) {i j k : ι}
    (hki : k ≠ i) (hkj : k ≠ j) (ε : ℝ) : splitCoord p i j ε k = p.coord k := by
  classical
  simp [splitCoord, hki, hkj]

end ProbabilityVector
end
end EntropyConstrainedMissingMass
