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

/--
@isnad1 id=continuo.0h1v.s4.ad0d60f22583 from=translated src=- shape=f736e2c1 vocab=70e6f4b6
-/
theorem continuous_splitEntropyIncrement (a : ℝ) : Continuous (splitEntropyIncrement a) := by
  unfold splitEntropyIncrement
  fun_prop

/--
@isnad1 id=eq.0h1v.s4.aa6d5b72fdf4 from=translated src=- shape=1d838610 vocab=9b3acbba
-/
@[simp] theorem splitEntropyIncrement_zero (a : ℝ) : splitEntropyIncrement a 0 = 0 := by
  simp [splitEntropyIncrement]

/--
@isnad1 id=tendsto.0h1v.s5.090644c70ff3 from=translated src=- shape=3a50da46 vocab=11d3153c
-/
theorem tendsto_splitEntropyIncrement_zero (a : ℝ) :
    Tendsto (splitEntropyIncrement a) (𝓝 0) (𝓝 0) := by
  simpa only [splitEntropyIncrement_zero] using (continuous_splitEntropyIncrement a).tendsto 0

/--
@isnad1 id=lt.2h2v.s5.ccb9bc74b74f from=translated src=- shape=909fdf01 vocab=9a649c45
-/
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

/--
@isnad1 id=eq.1h5v.s5.7f6cc36ba7e9 from=translated src=- shape=2eb18ffe vocab=a8a87109
-/
theorem splitCoord_i (p : ProbabilityVector ι) {i j : ι} (hij : i ≠ j) (ε : ℝ) :
    splitCoord p i j ε i = p.coord i - ε := by
  classical
  simp [splitCoord, hij]

/--
@isnad1 id=eq.0h5v.s4.f3b3c5777557 from=translated src=- shape=d438af23 vocab=35829f9c
-/
@[simp] theorem splitCoord_j (p : ProbabilityVector ι) (i j : ι) (ε : ℝ) :
    splitCoord p i j ε j = ε := by
  classical
  simp [splitCoord]

/--
@isnad1 id=eq.2h6v.s5.5ce83faee166 from=translated src=- shape=2a74bc44 vocab=15947ea2
-/
theorem splitCoord_other (p : ProbabilityVector ι) {i j k : ι}
    (hki : k ≠ i) (hkj : k ≠ j) (ε : ℝ) : splitCoord p i j ε k = p.coord k := by
  classical
  simp [splitCoord, hki, hkj]

end ProbabilityVector
end
end EntropyConstrainedMissingMass
