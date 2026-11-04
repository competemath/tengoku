import Tengoku.Seed.Analysis.SpecialFunctions.Log.Deriv
import Tengoku.Seed.Analysis.Calculus.Deriv.MeanValue
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Strict scalar inequalities in the exclusion of heavy candidates for t=1,2.
These inequalities do not assume or assert the constrained second-variation condition. -/

namespace EntropyConstrainedMissingMass

noncomputable def logRatioGap (r : ℝ) : ℝ := r - 1 / r - 2 * Real.log r

/--
@isnad1 id=eq.0h0v.s3.856e67e53eee from=translated src=- shape=3c26ae4f vocab=22ea5b5f
-/
@[simp] theorem logRatioGap_one : logRatioGap 1 = 0 := by simp [logRatioGap]

noncomputable def smallSampleNumerator (m r : ℝ) : ℝ :=
  (r - 1) * (4 * m + r - 3) - (4 * m + 4 * r - 6) * Real.log r

/--
@isnad1 id=eq.0h1v.s4.9d9a62dab5b9 from=translated src=- shape=1d838610 vocab=9b00b75b
-/
@[simp] theorem smallSampleNumerator_one (m : ℝ) : smallSampleNumerator m 1 = 0 := by
  simp [smallSampleNumerator]

/--
@isnad1 id=eq.0h2v.s6.37392cad776c from=translated src=- shape=69e1acd1 vocab=11403ff5
-/
theorem smallSampleNumerator_decompose (m r : ℝ) :
    smallSampleNumerator m r = smallSampleNumerator 2 r +
      4 * (m - 2) * (r - 1 - Real.log r) := by
  unfold smallSampleNumerator
  ring

/--
@isnad1 id=lt.1h1v.s5.7d5694bd942b from=translated src=- shape=a0678fc6 vocab=476036cf
-/
theorem logarithmic_mean_ratio_gt_one {r : ℝ} (hr : 1 < r) :
    1 < (r - 1) / Real.log r := by
  apply (one_lt_div (Real.log_pos hr)).mpr
  exact Real.log_lt_sub_one_of_pos (by linarith) (by linarith)

end EntropyConstrainedMissingMass
